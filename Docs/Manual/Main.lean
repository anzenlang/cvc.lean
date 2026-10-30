/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual

import CvcManual

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open CvcManual

/-- Code styling for the manual, overriding verso's all-black defaults. -/
def codeStyle : CSS := r#"
:root {
  --verso-code-font-family: "JetBrains Mono", "Fira Code", "SF Mono", Menlo, Consolas, monospace;
  --verso-code-color: #24292f;
  --verso-code-keyword-color: #8250df;
  --verso-code-keyword-weight: 600;
  --verso-code-const-color: #0550ae;
  --verso-code-var-color: #953800;
  --verso-code-var-style: normal;
}
.hl.lean .comment { color: #6e7781; font-style: italic; }
.hl.lean .literal, .hl.lean .number, .hl.lean .char { color: #0a3069; }
.hl.lean.block {
  display: block;
  margin-left: 0;
  padding: 0.75rem 1rem;
  background: #f6f8fa;
  border: 1px solid #d0d7de;
  border-radius: 6px;
  overflow-x: auto;
  font-size: 0.9em;
  line-height: 1.45;
}
.hl.lean.inline {
  padding: 0.1em 0.3em;
  background: #f6f8fa;
  border-radius: 4px;
  font-size: 0.9em;
}
"#

/-- The side table of contents lists only the current page's direct sub-sections.

Verso lists every docstring of the page there too, and every nested section when sub-sections share
the page, which makes a long page unreadable. It has no setting for this, so the extra entries are
hidden: a section entry is a `header head-N` span, `N` its nesting level, and a docstring entry is a
bare link.
-/
def tocStyle : CSS := r#"
#toc .split-toc > ol > li:not(:has(.header)),
#toc .split-toc > ol > li:has(.header:not(.head-1)) {
  display: none;
}
"#

/-- Where the API reference built by doc-gen4 is published. -/
def apiRoot : String := "https://adrienchampion.github.io/cvc.lean/api"

/-- Links into the API reference, for every constant and module the manual's code mentions.

A constant goes through doc-gen4's `find` page, which redirects to the declaration's own page: its
URL needs the module the constant is declared in, which rendering does not know. The API reference
documents the library together with everything it imports, core and the standard library included,
so only a definition the manual itself makes in an example has no page there, and gets no link.
-/
def apiTargets (state : TraverseState) : Code.LinkTargets Manual.TraverseContext where
  const x ctxt? :=
    if (state.exampleLinks x.toString ctxt?).isEmpty then
      #[{
        shortDescription := "api"
        description := s!"API documentation for {x}"
        href := s!"{apiRoot}/find/?pattern={System.Uri.escapeUri x.toString}#doc"
      }]
    else #[]
  moduleName m _ := #[{
    shortDescription := "api"
    description := s!"API documentation for module {m}"
    href := s!"{apiRoot}/{"/".intercalate (m.components.map toString)}.html"
  }]

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  extraCss := {codeStyle, tocStyle}
  htmlDepth := 2
  linkTargets state remotes := state.localTargets ++ remotes.remoteTargets ++ apiTargets state

def main := manualMain (%doc CvcManual) (config := config)
