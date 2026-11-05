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

@[default_target]
lean_lib Cvc

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
