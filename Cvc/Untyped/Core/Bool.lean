/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
-- `mkBool`/`mkInt` back the unit elements of the `N'` variants

public import Cvc.Ext
public meta import Cvc.Ext
public import Cvc.Gen.Term
public import Cvc.Untyped.Core.Value
public import Cvc.Spec.Bool



/-! # Generated Boolean and sort-generic constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.Bool

/-- A symbol of the sort `α` describes.

`mkSymbol` takes the sort itself; this names it by the Lean type denoting it.
-/
def mkSymbolAs (α : Type) [ToTyp α] (name : String) : Env Term := do
  mkSymbol (← Srt.of α) name



/-! ## Values -/

@[inherit_doc T.isBooleanValue]
def isBoolValue (term : Term) : Bool := T.isBooleanValue term.toUnsafe
/-- The boolean a term denotes, failing if it denotes none. -/
def getBoolValue (term : Term) : Res Bool :=
  T.getBooleanValue term.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getBoolValue]
def getBoolValue? (term : Term) : Option Bool := T.getBooleanValue? term.toUnsafe

instance : SrtLike Bool where
  valueToTerm := mkBool
  termToValue t := t.getBoolValue



/-! ## The DSL's literals for this theory

Declared here rather than in `Cvc.Ext` so that the grammar a user gets is the grammar of the
theories they imported: without this module, `smt!` does not accept them at all. The expander's own
machinery lives in `Cvc.Ext`, never in `Cvc`.
-/

public meta section

open Lean

/-- Conditional, `if c then t else e`. -/
syntax (name := smtIte)
  withPosition(
    "if " smtTerm (colGe " then " smtTerm) (colGe " else " (colGe smtTerm))
  )
: smtTerm

namespace Ext open Cvc.Ext

/-! `true` and `false` parse as *identifiers* in this category, so they are not a rule of their own
— this alternative claims those two names and declines every other identifier, which then falls
through to whatever else handles one.
-/

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.untyped do Macro.throwUnsupported
    let stx := t.raw
    match stx.getKind with
    | ``smtIte =>
      let args ← #[stx[1], stx[3], stx[5]].mapM (deferSmt layer)
      bindArgs args fun ids => `($(layer.op `ite) $(ids[0]!) $(ids[1]!) $(ids[2]!))
    | ``Cvc.smtIdent =>
      let id : Ident := ⟨stx[0]⟩
      match id.getId with
      | `true => `($(layer.op `mkTrue))
      | `false => `($(layer.op `mkFalse))
      | _ => Macro.throwUnsupported
    | _ => Macro.throwUnsupported

end Ext

end
