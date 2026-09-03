/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

public import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.Theory.BitVec
public import Cvc.Types.Float
public import Cvc.Spec.Float



/-! # Generated Float constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.Float

/-- A rounding-mode value.

Hand-written rather than specified: the conversion of the Lean enumeration into cvc5's is private,
so no `tm` entry can name it.
-/
def mkRoundingMode (rm : Cvc.Float.RoundingMode) : Env Term :=
  runUnsafe fun tm => tm.mkRoundingMode rm.toUnsafe



/-! ## Values

A rounding mode is an enum, so it goes to a term directly. A floating-point value is either one of
the five distinguished constants or a bit pattern, and reading one back needs the sort to recover
the exponent and significand sizes.
-/

@[inherit_doc T.isRoundingModeValue]
def isRoundingModeValue (term : Term) : Bool := T.isRoundingModeValue term.toUnsafe

/-- The rounding mode a term denotes, failing if it denotes none. -/
def getRoundingModeValue (term : Term) : Res Cvc.Float.RoundingMode := do
  let rm ← T.getRoundingModeValue term.toUnsafe |>.mapError Error.ofUnsafe
  return Cvc.Float.RoundingMode.ofUnsafe rm

instance : SrtLike Cvc.Float.RoundingMode where
  valueToTerm := mkRoundingMode
  termToValue t := t.getRoundingModeValue

/-! ### Floating-point values

`isFloatValue` holds of a constant, which cvc5 always canonicalises into a bit pattern — so the
five predicates below classify a pattern rather than a distinct representation.
-/

@[inherit_doc T.isFloatingPointValue]
def isFloatValue (term : Term) : Bool := T.isFloatingPointValue term.toUnsafe
@[inherit_doc T.isFloatingPointNaN]
def isFloatNaN (term : Term) : Bool := T.isFloatingPointNaN term.toUnsafe
@[inherit_doc T.isFloatingPointPosInf]
def isFloatPosInf (term : Term) : Bool := T.isFloatingPointPosInf term.toUnsafe
@[inherit_doc T.isFloatingPointNegInf]
def isFloatNegInf (term : Term) : Bool := T.isFloatingPointNegInf term.toUnsafe
@[inherit_doc T.isFloatingPointPosZero]
def isFloatPosZero (term : Term) : Bool := T.isFloatingPointPosZero term.toUnsafe
@[inherit_doc T.isFloatingPointNegZero]
def isFloatNegZero (term : Term) : Bool := T.isFloatingPointNegZero term.toUnsafe

/-- The exponent size, significand size and bit pattern of a constant floating-point term. -/
def getFloatComponents (term : Term) : Res (Nat × Nat × Term) := do
  let (exp, sig, bv) ← T.getFloatingPointValue term.toUnsafe |>.mapError Error.ofUnsafe
  let bv : Term := bv
  return (exp.toNat, sig.toNat, bv)

@[inherit_doc getFloatComponents]
def getFloatComponents? (term : Term) : Option (Nat × Nat × Term) :=
  term.getFloatComponents.toOption

namespace Float

/-- The floating-point term denoting a value of known exponent and significand sizes. -/
def toTerm : (f : Cvc.Float exp sig) → Env Term
  | .posInf => mkFloatPosInf exp sig
  | .negInf => mkFloatNegInf exp sig
  | .nan => mkFloatNaN exp sig
  | .posZero => mkFloatPosZero exp sig
  | .negZero => mkFloatNegZero exp sig
  | .ofBitVec bv => do mkFloat exp sig (← mkValue bv)

/-- The floating-point value a constant term denotes, at whatever sizes it turns out to have. -/
def ofTermErased (term : Term) : Env Cvc.Float.Erased := do
  if let some (exp, sig, bv) := term.getFloatComponents? then
    return {exp, sig, get := .ofBitVec (← extractValue bv)}
  let srt ← term.getSort
  let exp ← UInt32.toNat <$> srt.getFloatingPointExponentSize
  let sig ← UInt32.toNat <$> srt.getFloatingPointSignificandSize
  let mk (f : Cvc.Float exp sig) : Env Cvc.Float.Erased := return {exp, sig, get := f}
  if term.isFloatPosInf then mk .posInf
  else if term.isFloatNegInf then mk .negInf
  else if term.isFloatNaN then mk .nan
  else if term.isFloatPosZero then mk .posZero
  else if term.isFloatNegZero then mk .negZero
  else throwUser s!"expected a constant floating-point term, got `{term}`"

/-- The floating-point value a constant term denotes, failing unless the sizes are the expected. -/
def ofTerm (term : Term) : Env (Cvc.Float exp sig) := do
  let ⟨exp', sig', float⟩ ← ofTermErased term
  if h : exp' = exp ∧ sig' = sig then return h.left ▸ h.right ▸ float
  else throwUser <|
    s!"expected a floating-point constant of exp/sig {exp}/{sig}, got {exp'}/{sig'}: `{term}`"

end Float

instance : SrtLike (Cvc.Float exp sig) where
  valueToTerm := Float.toTerm
  termToValue := Float.ofTerm
