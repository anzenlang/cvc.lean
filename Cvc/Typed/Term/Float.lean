/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Untyped.Term.Defs
import all Cvc.Typed.Term.Defs

public import Cvc.Types.Float
public import Cvc.Untyped.Term.Float
public import Cvc.Typed.Term.Defs
public import Cvc.Typed.Term.Value
public import Cvc.Gen
public import Cvc.Spec.Float



/-! # Generated Float constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Float

@[inherit_doc T.mkRoundingMode]
def mkRoundingMode (rm : Cvc.Float.RoundingMode) : Env (Term Cvc.Float.RoundingMode) :=
  T.mkRoundingMode rm



/-! ## Values -/

@[inherit_doc T.isRoundingModeValue]
def isRoundingModeValue (term : Term Cvc.Float.RoundingMode) : Bool := T.isRoundingModeValue term

@[inherit_doc T.isFloatValue]
def isFloatValue (term : Term (Cvc.Float exp sig)) : Bool := T.isFloatValue term
@[inherit_doc T.isFloatNaN]
def isFloatNaN (term : Term (Cvc.Float exp sig)) : Bool := T.isFloatNaN term
@[inherit_doc T.isFloatPosInf]
def isFloatPosInf (term : Term (Cvc.Float exp sig)) : Bool := T.isFloatPosInf term
@[inherit_doc T.isFloatNegInf]
def isFloatNegInf (term : Term (Cvc.Float exp sig)) : Bool := T.isFloatNegInf term
@[inherit_doc T.isFloatPosZero]
def isFloatPosZero (term : Term (Cvc.Float exp sig)) : Bool := T.isFloatPosZero term
@[inherit_doc T.isFloatNegZero]
def isFloatNegZero (term : Term (Cvc.Float exp sig)) : Bool := T.isFloatNegZero term

/-- The exponent size, significand size and bit pattern of a constant floating-point term.

The pattern is sort-erased: its own index would be `BitVec (exp + sig)`, which the *values* the
sizes carry decide, not the term's index.
-/
def getFloatComponents (term : Term (Cvc.Float exp sig))
: Res (Nat × Nat × Untyped.Term) := T.getFloatComponents term


@[inherit_doc T.getRoundingModeValue]
def getRoundingModeValue (term : Term Cvc.Float.RoundingMode) : Res Cvc.Float.RoundingMode :=
  T.getRoundingModeValue term

instance : SrtLike Float.RoundingMode where
  valueToTerm := mkRoundingMode
  termToValue t := getRoundingModeValue t

/-- The floating-point term denoting a value. -/
def mkFloatValue
: (f : Cvc.Float exp sig) → Env (Term (Cvc.Float exp sig)) := T.Float.toTerm

/-- The floating-point value a constant term denotes. -/
def getFloatValue : Term (Cvc.Float exp sig) → Env (Cvc.Float exp sig) := T.Float.ofTerm

instance : SrtLike (Cvc.Float exp sig) where
  valueToTerm := mkFloatValue
  termToValue := getFloatValue
