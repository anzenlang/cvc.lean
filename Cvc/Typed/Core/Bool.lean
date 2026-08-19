/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs

public import Cvc.Untyped.Core.Bool
public meta import Cvc.Ext
public import Cvc.Typed.Core.Defs
public import Cvc.Typed.Core.Value
public import Cvc.Gen
public import Cvc.Spec.Bool



/-! # Generated Boolean and sort-generic constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Bool

/-- A symbol of the sort `α` describes, naming `α` explicitly. -/
def mkSymbolAs (α : Type) [ToTyp α] (name : String) : Env (Term α) := mkSymbol name



/-! ## Values -/

@[inherit_doc T.isBoolValue]
def isBoolValue (term : Term Bool) : Bool := T.isBoolValue term
@[inherit_doc T.getBoolValue]
def getBoolValue (term : Term Bool) : Res Bool := T.getBoolValue term
@[inherit_doc T.getBoolValue?]
def getBoolValue? (term : Term Bool) : Option Bool := T.getBoolValue? term

instance : SrtLike Bool where
  valueToTerm := mkBool
  termToValue t := getBoolValue t



/-! ## The DSL's literals for this theory

Expanded here rather than in `Cvc.Ext` so that the grammar a user gets is the grammar of the
theories they imported: without this module, `smt!` does not accept them at all. The expander's own
machinery lives in `Cvc.Ext`, never in `Cvc`.
-/

public meta section

open Lean

namespace Ext open Cvc.Ext

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.typed do Macro.throwUnsupported
    let stx := t.raw
    match stx.getKind with
    | ``Cvc.Untyped.Term.smtIte =>
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
