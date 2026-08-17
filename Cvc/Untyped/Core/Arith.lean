/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
-- `mkBool`/`mkInt` back the unit elements of the `N'` variants

public import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Gen
public import Cvc.Spec.Arith



/-! # Generated arithmetic constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.Arith



/-! ## Values

`Nat` goes to a term but not back: the sort is `Int`, so reading one back would have to fail on a
negative value rather than answer.
-/

@[inherit_doc T.getRealOrIntegerValueSign]
def getSign (term : Term) : Res Int :=
  T.getRealOrIntegerValueSign term.toUnsafe |>.mapError Error.ofUnsafe

/-! ### Machine-width views

An SMT integer is unbounded, so these say whether a value happens to fit a machine word and hand it
over if it does. They are views of `getIntValue`, not a different value.
-/

@[inherit_doc T.isInt32Value]
def isInt32Value (term : Term) : Bool := T.isInt32Value term.toUnsafe
@[inherit_doc T.getInt32Value]
def getInt32Value (term : Term) : Res Int32 :=
  T.getInt32Value term.toUnsafe |>.mapError Error.ofUnsafe

@[inherit_doc T.isInt64Value]
def isInt64Value (term : Term) : Bool := T.isInt64Value term.toUnsafe
@[inherit_doc T.getInt64Value]
def getInt64Value (term : Term) : Res Int64 :=
  T.getInt64Value term.toUnsafe |>.mapError Error.ofUnsafe

@[inherit_doc T.isUInt32Value]
def isUInt32Value (term : Term) : Bool := T.isUInt32Value term.toUnsafe
@[inherit_doc T.getUInt32Value]
def getUInt32Value (term : Term) : Res UInt32 :=
  T.getUInt32Value term.toUnsafe |>.mapError Error.ofUnsafe

@[inherit_doc T.isUInt64Value]
def isUInt64Value (term : Term) : Bool := T.isUInt64Value term.toUnsafe
@[inherit_doc T.getUInt64Value]
def getUInt64Value (term : Term) : Res UInt64 :=
  T.getUInt64Value term.toUnsafe |>.mapError Error.ofUnsafe

/-- Whether a term denotes a real that fits a 32-bit numerator and denominator. -/
def isReal32Value (term : Term) : Bool := T.isReal32Value term.toUnsafe
/-- The numerator and denominator of a real value, at 32 bits. -/
def getReal32Value (term : Term) : Res (Int32 × UInt32) :=
  T.getReal32Value term.toUnsafe |>.mapError Error.ofUnsafe

/-- Whether a term denotes a real that fits a 64-bit numerator and denominator. -/
def isReal64Value (term : Term) : Bool := T.isReal64Value term.toUnsafe
/-- The numerator and denominator of a real value, at 64 bits. -/
def getReal64Value (term : Term) : Res (Int64 × UInt64) :=
  T.getReal64Value term.toUnsafe |>.mapError Error.ofUnsafe

/-! ### Real algebraic numbers

A real algebraic number is not a rational, so it has no `getRatValue`. It is described instead by a
polynomial it is a root of, together with an interval isolating that root.
-/

@[inherit_doc T.isRealAlgebraicNumber]
def isRealAlgebraicNumber (term : Term) : Bool := T.isRealAlgebraicNumber term.toUnsafe

@[inherit_doc T.getRealAlgebraicNumberDefiningPolynomial]
def getRealAlgebraicNumberPolynomial (term : Term) (v : Term) : Env Term :=
  T.getRealAlgebraicNumberDefiningPolynomial term.toUnsafe v.toUnsafe |>.mapError Error.ofUnsafe

@[inherit_doc T.getRealAlgebraicNumberLowerBound]
def getRealAlgebraicNumberLowerBound (term : Term) : Env Term :=
  T.getRealAlgebraicNumberLowerBound term.toUnsafe |>.mapError Error.ofUnsafe

@[inherit_doc T.getRealAlgebraicNumberUpperBound]
def getRealAlgebraicNumberUpperBound (term : Term) : Env Term :=
  T.getRealAlgebraicNumberUpperBound term.toUnsafe |>.mapError Error.ofUnsafe


@[inherit_doc T.isIntegerValue]
def isIntValue (term : Term) : Bool := T.isIntegerValue term.toUnsafe
/-- The integer a term denotes, failing if it denotes none. -/
def getIntValue (term : Term) : Res Int :=
  T.getIntegerValue term.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getIntValue]
def getIntValue? (term : Term) : Option Int := T.getIntegerValue? term.toUnsafe

@[inherit_doc T.isRealValue]
def isRealValue (term : Term) : Bool := T.isRealValue term.toUnsafe
/-- The real a term denotes as a string, failing if it denotes none. -/
def getRealValue (term : Term) : Res String :=
  T.getRealValue term.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getRealValue]
def getRealValue? (term : Term) : Option String := T.getRealValue? term.toUnsafe
/-- The real a term denotes as a `Rat`, failing if it denotes none. -/
def getRatValue (term : Term) : Res Rat :=
  T.getRationalValue term.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getRatValue]
def getRatValue? (term : Term) : Option Rat := T.getRationalValue? term.toUnsafe

instance : SrtLike Int where
  valueToTerm := mkInt
  termToValue t := t.getIntValue

instance : ValueToTerm Nat where
  valueToTerm n := mkInt n

instance : SrtLike Rat where
  valueToTerm := mkReal
  termToValue t := t.getRatValue
