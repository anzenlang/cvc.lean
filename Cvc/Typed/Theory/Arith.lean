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

public import Cvc.Untyped.Theory.Arith
public meta import Cvc.Ext
public import Cvc.Typed.Core.Defs
public import Cvc.Typed.Core.Value
public import Cvc.Spec.Arith



/-! # Generated arithmetic constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Arith



/-! ## Values

`Nat` goes to a term but not back: the sort is `Int`, so reading one back would have to fail on a
negative value rather than answer.
-/

/-- The sign of an arithmetic value: negative, zero or positive as `-1`, `0`, `1`. -/
def getSign [ToTyp α] [IsArith α] (term : Term α) : Res Int := T.getSign term

/-! ### Machine-width views

An SMT integer is unbounded, so these say whether a value happens to fit a machine word and hand it
over if it does. They are views of `getIntValue`, not a different value.
-/

@[inherit_doc T.isInt32Value]
def isInt32Value (term : Term Int) : Bool := T.isInt32Value term
@[inherit_doc T.getInt32Value]
def getInt32Value (term : Term Int) : Res Int32 := T.getInt32Value term

@[inherit_doc T.isInt64Value]
def isInt64Value (term : Term Int) : Bool := T.isInt64Value term
@[inherit_doc T.getInt64Value]
def getInt64Value (term : Term Int) : Res Int64 := T.getInt64Value term

@[inherit_doc T.isUInt32Value]
def isUInt32Value (term : Term Int) : Bool := T.isUInt32Value term
@[inherit_doc T.getUInt32Value]
def getUInt32Value (term : Term Int) : Res UInt32 := T.getUInt32Value term

@[inherit_doc T.isUInt64Value]
def isUInt64Value (term : Term Int) : Bool := T.isUInt64Value term
@[inherit_doc T.getUInt64Value]
def getUInt64Value (term : Term Int) : Res UInt64 := T.getUInt64Value term

@[inherit_doc T.isReal32Value]
def isReal32Value (term : Term Rat) : Bool := T.isReal32Value term
@[inherit_doc T.getReal32Value]
def getReal32Value (term : Term Rat) : Res (Int32 × UInt32) := T.getReal32Value term

@[inherit_doc T.isReal64Value]
def isReal64Value (term : Term Rat) : Bool := T.isReal64Value term
@[inherit_doc T.getReal64Value]
def getReal64Value (term : Term Rat) : Res (Int64 × UInt64) := T.getReal64Value term

/-! ### Real algebraic numbers

A real algebraic number is not a rational, so it has no `getRatValue`. It is described instead by a
polynomial it is a root of, together with an interval isolating that root.
-/

@[inherit_doc T.isRealAlgebraicNumber]
def isRealAlgebraicNumber (term : Term Rat) : Bool := T.isRealAlgebraicNumber term

@[inherit_doc T.getRealAlgebraicNumberPolynomial]
def getRealAlgebraicNumberPolynomial (term : Term Rat) (v : Term Rat) : Env (Term Rat) :=
  T.getRealAlgebraicNumberPolynomial term v

@[inherit_doc T.getRealAlgebraicNumberLowerBound]
def getRealAlgebraicNumberLowerBound (term : Term Rat) : Env (Term Rat) :=
  T.getRealAlgebraicNumberLowerBound term

@[inherit_doc T.getRealAlgebraicNumberUpperBound]
def getRealAlgebraicNumberUpperBound (term : Term Rat) : Env (Term Rat) :=
  T.getRealAlgebraicNumberUpperBound term


@[inherit_doc T.isIntValue]
def isIntValue (term : Term Int) : Bool := T.isIntValue term
@[inherit_doc T.getIntValue]
def getIntValue (term : Term Int) : Res Int := T.getIntValue term
@[inherit_doc T.getIntValue?]
def getIntValue? (term : Term Int) : Option Int := T.getIntValue? term

@[inherit_doc T.isRealValue]
def isRealValue (term : Term Rat) : Bool := T.isRealValue term
@[inherit_doc T.getRealValue]
def getRealValue (term : Term Rat) : Res String := T.getRealValue term
@[inherit_doc T.getRealValue?]
def getRealValue? (term : Term Rat) : Option String := T.getRealValue? term
@[inherit_doc T.getRatValue]
def getRatValue (term : Term Rat) : Res Rat := T.getRatValue term
@[inherit_doc T.getRatValue?]
def getRatValue? (term : Term Rat) : Option Rat := T.getRatValue? term

instance : SrtLike Int where
  valueToTerm := mkInt
  termToValue t := getIntValue t

instance : SrtLike Rat where
  valueToTerm := mkReal
  termToValue t := getRatValue t



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
    | ``Cvc.Untyped.Term.smtNum => do
      let n : TSyntax `term := ⟨stx[0]⟩
      `($(layer.op `mkInt) ($n : Int))
    | ``Cvc.Untyped.Term.smtSci => do
      let r : TSyntax `term := ⟨stx[0]⟩
      `($(layer.op `mkReal) $r)
    | _ => Macro.throwUnsupported

end Ext

end
