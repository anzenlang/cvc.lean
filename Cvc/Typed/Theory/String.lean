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

public import Cvc.Untyped.Theory.String
public meta import Cvc.Ext
public import Cvc.Typed.Core.Value
public import Cvc.Gen
public import Cvc.Spec.String



/-! # Generated String constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.String



/-! ## Values -/

@[inherit_doc T.isStringValue]
def isStringValue (term : Term String) : Bool := T.isStringValue term
@[inherit_doc T.getStringValue]
def getStringValue (term : Term String) : Res String := T.getStringValue term
@[inherit_doc T.getStringValue?]
def getStringValue? (term : Term String) : Option String := T.getStringValue? term

instance : SrtLike String where
  valueToTerm s := mkString s false
  termToValue t := getStringValue t



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
    unless t.raw.getKind == ``Cvc.Untyped.Term.smtStr do Macro.throwUnsupported
    let s : TSyntax `term := ⟨t.raw[0]⟩
    `($(layer.op `mkString) $s false)

end Ext

end
