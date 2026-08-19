/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

public import Cvc.Ext
public meta import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Gen.Term
public import Cvc.Spec.String



/-! # Generated String constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.String



/-! ## Values -/

@[inherit_doc T.isStringValue]
def isStringValue (term : Term) : Bool := T.isStringValue term.toUnsafe

/-- The string a term denotes, failing if it denotes none.

lean-cvc5 does not expose cvc5's string-value accessor, so this reads the term's own printed form,
which is the SMT-LIB string literal.
-/
def getStringValue (term : Term) : Res String :=
  if term.isStringValue then
    let s := toString term
    if s.startsWith '"' ∧ s.endsWith '"' then return s.drop 1 |>.dropEnd 1 |>.toString
    else throwUser s!"failed to retrieve string value of term `{s}`"
  else throwUser "cannot extract the string value of a term that denotes no string"

@[inherit_doc getStringValue]
def getStringValue? (term : Term) : Option String := term.getStringValue.toOption

instance : SrtLike String where
  valueToTerm s := mkString s false
  termToValue t := t.getStringValue



/-! ## The DSL's literals for this theory

Declared here rather than in `Cvc.Ext` so that the grammar a user gets is the grammar of the
theories they imported: without this module, `smt!` does not accept them at all. The expander's own
machinery lives in `Cvc.Ext`, never in `Cvc`.
-/

public meta section

open Lean

/-- String literal. -/
syntax:max (name := smtStr) str : smtTerm

namespace Ext open Cvc.Ext

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.untyped do Macro.throwUnsupported
    unless t.raw.getKind == ``smtStr do Macro.throwUnsupported
    let s : TSyntax `term := ⟨t.raw[0]⟩
    `($(layer.op `mkString) $s false)

end Ext

end
