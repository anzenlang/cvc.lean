/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Lake
open Lake DSL

package cvc {
  precompileModules := true
  testDriver := "cvcTests"
}

require "abdoo8080" / cvc5

/-! ## TEMPORARY: a glibc compatibility shim for cvc5 on Linux

lean-cvc5's Linux cvc5 libraries were built against glibc 2.38 or later and reference the C23
variants `__isoc23_strtol` and `__isoc23_fscanf`, which the older glibc Lean links executables
against does not have: without this shim, no executable using the library links on Linux, the
manual's included. `Cvc/glibc_compat.c` defines the two, forwarding to the classic functions, and is
linked into everything that links `Cvc` on Linux; elsewhere it is neither compiled nor linked. It is
compiled with the C compiler Lean ships, so a user needs no C compiler of their own. Remove it once
lean-cvc5 ships a cvc5 built against an older glibc.
-/

input_file glibcCompat.c where
  path := "Cvc" / "glibc_compat.c"
  text := true

target glibcCompat.o pkg : System.FilePath := do
  let srcJob ← glibcCompat.c.fetch
  let oFile := pkg.buildDir / "Cvc" / "glibc_compat.o"
  -- Lean's own compiler, as Lean's C is compiled: a plain `buildO` runs whatever `clang` the
  -- system's `PATH` has, if any
  buildLeanO oFile srcJob (traceArgs := #["-std=c11", "-fPIC"])

/-! ## Releases carry the lean-cvc5 build they were made with

lean-cvc5 fetches files from two releases of its own when it is built: its build archive, which
Lake falls back from by building it from source, and cvc5's static libraries, without which it
cannot build at all. A release of this library attaches, for each platform it supports, a bundle of
both — cvc5's static libraries and lean-cvc5's build directory — so that depending on a release
keeps working whatever becomes of those files.

`leanCvc5Bundle` restores the bundle when this package is a git dependency checked out at a release
tag, before Lake processes lean-cvc5. lean-cvc5 then fetches nothing: Lake skips a dependency's
build archive when its build directory exists, and lean-cvc5 skips downloading cvc5 when the trace
the bundle carries says the download was done. If the bundle cannot be fetched, lean-cvc5 fetches
its own files as it always does. `lake run packLeanCvc5Bundle <dir>` packs the bundle; the release
workflow runs it on each platform and attaches the result.
-/

/-- The file name of the lean-cvc5 bundle for the platform Lake runs on. -/
def leanCvc5BundleName : String :=
  s!"lean-cvc5-{System.Platform.target}.tar.gz"

/-- The directory under `dir` holding cvc5's static release, `cvc5-<os>-<arch>-static`. -/
def cvc5StaticDir? (dir : System.FilePath) : IO (Option String) := do
  return (← dir.readDir).findSome? fun entry =>
    let name := entry.fileName
    if name.startsWith "cvc5-" && name.endsWith "-static" then some name else none

/-- Runs `cmd args` in `cwd`, failing with its error output if it fails. -/
def runOrFail (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO Unit := do
  let out ← IO.Process.output { cmd, args, cwd }
  unless out.exitCode == 0 do
    throw <| .userError s!"`{cmd}` exited with code {out.exitCode}: {out.stderr.trimAscii.toString}"

/-- Downloads the bundle at `url` and moves its contents into `leanCvc5`, lean-cvc5's directory.

`staging` is a scratch directory. Nothing is moved unless the whole bundle was fetched and unpacked.
-/
def restoreLeanCvc5 (url : String) (staging leanCvc5 : System.FilePath) : IO Unit := do
  if ← staging.pathExists then IO.FS.removeDirAll staging
  IO.FS.createDirAll staging
  let archive := staging / leanCvc5BundleName
  runOrFail "curl" #["-sSfL", "--retry", "3", "-o", archive.toString, url]
  runOrFail "tar" #["-xzf", archive.toString, "-C", staging.toString]
  let some cvc5Dir ← cvc5StaticDir? staging
    | throw <| .userError "the bundle holds no cvc5 release"
  unless ← (staging / ".lake" / "build").pathExists do
    throw <| .userError "the bundle holds no build directory"
  if ← (leanCvc5 / cvc5Dir).pathExists then IO.FS.removeDirAll (leanCvc5 / cvc5Dir)
  IO.FS.rename (staging / cvc5Dir) (leanCvc5 / cvc5Dir)
  IO.FS.createDirAll (leanCvc5 / ".lake")
  IO.FS.rename (staging / ".lake" / "build") (leanCvc5 / ".lake" / "build")
-- The build directory goes last: its presence is what stops Lake from fetching lean-cvc5's archive,
-- so a failure before it leaves lean-cvc5 to fetch its own files as usual.

/-- Restores lean-cvc5 from this release's bundle, when this package is a dependency at a release.

Does nothing unless this package is a git dependency checked out at a tag, lean-cvc5 has no build
directory yet, and the platform is not Windows, for which releases carry no bundle. The bundle is
looked up where Lake looks up release archives: on the release of that tag, in the repository this
package was cloned from. Failing to restore it is only a warning, since lean-cvc5 then fetches its
own files.
-/
target leanCvc5Bundle pkg : Unit := do
  let some leanCvc5 ← findPackageByName? `cvc5
    | error "lean-cvc5 is not in the workspace"
  -- on Windows the bundle never exists, and failing to find it would only print a warning
  if pkg.isRoot || System.Platform.isWindows || (← leanCvc5.buildDir.pathExists) then
    return pure ()
  let some repo := pkg.remoteUrl? | return pure ()
  let some tag ← (GitRepo.mk pkg.dir).findTag? | return pure ()
  let repo := if repo.endsWith ".git" then (repo.dropEnd 4).copy else repo
  let url := s!"{repo}/releases/download/{tag}/{leanCvc5BundleName}"
  let staging := pkg.buildDir / "leanCvc5Bundle"
  match ← (restoreLeanCvc5 url staging leanCvc5.dir).toBaseIO with
  | .ok () => logInfo s!"restored lean-cvc5 from {url}"
  | .error e => logWarning s!"could not restore lean-cvc5 from {url}, so lean-cvc5 fetches its own \
      files: {e}"
  discard <| (IO.FS.removeDirAll staging).toBaseIO
  return pure ()
-- It does its work while Lake computes the build's jobs rather than in a job of its own, and every
-- module of `Cvc` needs it: Lake finishes a library's `needs` before processing the imports of any
-- of its modules, so lean-cvc5 is restored before anything looks at it.
-- Failures are caught rather than logged as errors, since an error in the log fails the build.

/-- Packs this platform's lean-cvc5 bundle into the directory given as argument.

lean-cvc5 must have been built, by `lake build` for instance. The bundle holds cvc5's static release
— its executable and Java bindings left out, nothing linking them — lean-cvc5's build directory, and
lean-cvc5's licence. cvc5's release carries its own licences, GMP's LGPL among them.
-/
script packLeanCvc5Bundle (args) do
  let [dir] := args
    | throw <| .userError "expected one argument, the directory to pack the bundle into"
  let some leanCvc5 ← findPackageByName? `cvc5
    | throw <| .userError "lean-cvc5 is not in the workspace"
  unless ← leanCvc5.buildDir.pathExists do
    throw <| .userError "lean-cvc5 has not been built: run `lake build` first"
  let some cvc5Dir ← cvc5StaticDir? leanCvc5.dir
    | throw <| .userError "lean-cvc5 holds no cvc5 release"
  IO.FS.createDirAll dir
  let archive ← IO.FS.realPath dir <&> (· / leanCvc5BundleName)
  runOrFail "tar" (cwd := leanCvc5.dir) #[
    "-czf", archive.toString, "--exclude", s!"{cvc5Dir}/bin", "--exclude", "*cvc5jni*",
    "LICENSE", cvc5Dir, ".lake/build"
  ]
  IO.println archive
  return 0

@[default_target]
lean_lib Cvc where
  moreLinkObjs := if System.Platform.isLinux then #[glibcCompat.o] else #[]
  needs := #[leanCvc5Bundle]

lean_lib cvcTests {
  globs := #[Glob.submodules `CvcTests, Glob.submodules `CvcExamples]
}



/-! ## Documentation

The manual (`CvcManual`, written with Verso) and the API reference (built by doc-gen4) are Lake
projects of their own. The manual's is part of the repository; the API reference's is generated
under `.lake`, being nothing but a doc-gen4 dependency matched to this project's toolchain. These
scripts build and serve them from here: `lake run buildManual`, `lake run serveManual`,
`lake run buildApiDocs` and `lake run serveApiDocs`. Serving builds first, then serves on
`http://localhost:8000` until interrupted; a port given as argument replaces 8000
(`lake run serveApiDocs 8001`), so that both can be served at once.
-/

/-- Variables the outer `lake` sets for its children. Left in place, they would make the `lake` of a
sub-project use the toolchain and paths of this one rather than its own. -/
def lakeEnvVars : Array String :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH",
    "LEAN_SRC_PATH", "LEAN", "ELAN", "ELAN_HOME", "LEAN_GITHASH", "ELAN_TOOLCHAIN",
    "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

/-- Runs `lake args` in the project at `dir`, under the toolchain that project names. -/
def lakeIn (dir : System.FilePath) (args : Array String) : IO UInt32 := do
  let toolchain := (← IO.FS.readFile (dir / "lean-toolchain")).trimAscii.toString
  let child ← IO.Process.spawn {
    cmd := "elan"
    args := #["run", "--install", toolchain, "lake"] ++ args
    cwd := dir
    env := lakeEnvVars.map (·, none)
  }
  child.wait

/-- Serves `dir` over HTTP until interrupted. -/
def serveDir (dir : System.FilePath) (port : Nat := 8000) : IO UInt32 := do
  IO.println s!"serving {dir} on http://localhost:{port}"
  let child ← IO.Process.spawn {
    cmd := "python3", args := #["-m", "http.server", toString port, "-d", dir.toString]
  }
  child.wait

/-- The port to serve on: the script's argument if it gave one, `8000` otherwise. -/
def portOf (args : List String) : IO Nat :=
  match args with
  | [] => return 8000
  | [port] => match port.toNat? with
    | some port => return port
    | none => throw <| .userError s!"expected a port number, got `{port}`"
  | _ => throw <| .userError "expected at most one argument, the port to serve on"

/-- The manual's project. -/
def manualDir : System.FilePath := __dir__ / "CvcManual"

/-- Where the API reference's project is generated: under `.lake`, with the build artifacts. -/
def apiDocsDir : System.FilePath := __dir__ / ".lake" / "docbuild"

/-- The doc-gen4 revision for a toolchain: the release's tag, `main` for anything else.

doc-gen4 tags one revision per Lean release and release candidate, named after it.
-/
def docGenRev (toolchain : String) : String :=
  match toolchain.splitOn ":" with
  | ["leanprover/lean4", version] => if version.startsWith "v4." then version else "main"
  | _ => "main"

/-- Generates the API reference's project, a doc-gen4 build of `Cvc` on this project's toolchain.

It shares this project's packages directory, so cvc5 is not fetched twice and the library is not
rebuilt, and pins doc-gen4 to the revision `docGenRev` reads off `lean-toolchain`, so a toolchain
bump carries doc-gen4 along. On the first run, and whenever that revision changes, doc-gen4 is
updated alone, which leaves the shared `cvc5` at the revision this project's manifest pins.
-/
def generateApiDocsProject : IO UInt32 := do
  let toolchain := (← IO.FS.readFile (__dir__ / "lean-toolchain")).trimAscii.toString
  let config := s!"name = \"docbuild\"
reservoir = false
packagesDir = \"../packages\"

[[require]]
name = \"cvc\"
path = \"../..\"

[[require]]
scope = \"leanprover\"
name = \"doc-gen4\"
rev = \"{docGenRev toolchain}\"
"
  IO.FS.createDirAll apiDocsDir
  IO.FS.writeFile (apiDocsDir / "lean-toolchain") s!"{toolchain}\n"
  let configFile := apiDocsDir / "lakefile.toml"
  -- nested, not `&&`: an action in a condition runs before the condition is evaluated, so reading a
  -- file that does not exist yet has to sit behind its own check
  if (← configFile.pathExists) && (← (apiDocsDir / "lake-manifest.json").pathExists) then
    if (← IO.FS.readFile configFile) == config then
      return 0
  IO.FS.writeFile configFile config
  lakeIn apiDocsDir #["update", "doc-gen4"]

/-- Generates the API reference's project, then builds the reference. -/
def buildApiDocsProject : IO UInt32 := do
  let code ← generateApiDocsProject
  if code != 0 then return code
  lakeIn apiDocsDir #["build", "Cvc:docs"]

/-- Builds the manual into `CvcManual/_out/html-multi`. -/
script buildManual do
  lakeIn manualDir #["exe", "docs"]

/-- Builds the manual, then serves it. -/
script serveManual (args) do
  let port ← portOf args
  let code ← lakeIn manualDir #["exe", "docs"]
  if code != 0 then return code
  serveDir (manualDir / "_out" / "html-multi") port

/-- Builds the API reference into `.lake/docbuild/.lake/build/doc`. -/
script buildApiDocs do
  buildApiDocsProject

/-- Builds the API reference, then serves it. -/
script serveApiDocs (args) do
  let port ← portOf args
  let code ← buildApiDocsProject
  if code != 0 then return code
  serveDir (apiDocsDir / ".lake" / "build" / "doc") port
