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
  globs := #[Glob.submodules `Cvc.Tests, Glob.submodules `Cvc.Examples]
}



/-! ## Documentation

The manual (`Docs/Manual`, written with Verso) and the API reference (`Docs/Api`, built by
doc-gen4) are Lake projects of their own, each on its own toolchain. These scripts build and serve
them from here: `lake run buildManual`, `lake run serveManual`, `lake run buildApiDocs` and
`lake run serveApiDocs`. Serving builds first, then serves on `http://localhost:8000` until
interrupted; a port given as argument replaces 8000 (`lake run serveApiDocs 8001`), so that both
can be served at once.
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
def manualDir : System.FilePath := __dir__ / "Docs" / "Manual"

/-- The API reference's project. -/
def apiDocsDir : System.FilePath := __dir__ / "Docs" / "Api"

/-- Builds the manual into `Docs/Manual/_out/html-multi`. -/
script buildManual do
  lakeIn manualDir #["exe", "docs"]

/-- Builds the manual, then serves it. -/
script serveManual (args) do
  let port ← portOf args
  let code ← lakeIn manualDir #["exe", "docs"]
  if code != 0 then return code
  serveDir (manualDir / "_out" / "html-multi") port

/-- Builds the API reference into `Docs/Api/.lake/build/doc`. -/
script buildApiDocs do
  lakeIn apiDocsDir #["build", "Cvc:docs"]

/-- Builds the API reference, then serves it. -/
script serveApiDocs (args) do
  let port ← portOf args
  let code ← lakeIn apiDocsDir #["build", "Cvc:docs"]
  if code != 0 then return code
  serveDir (apiDocsDir / ".lake" / "build" / "doc") port
