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

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  extraCss := {codeStyle}
  htmlDepth := 2

def main := manualMain (%doc CvcManual) (config := config)
