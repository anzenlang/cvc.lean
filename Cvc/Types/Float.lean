/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt



/-! # Floating-point values

The Lean type denoting a value of SMT sort `(_ FloatingPoint exp sig)`: one of the five
distinguished constants, or the bit pattern itself.

**`exp` and `sig` follow SMT-LIB, not IEEE-754 field widths.** `sig` counts the significand's
bits *including* the hidden leading one, so the stored pattern is one sign bit, `exp` exponent bits
and `sig - 1` stored significand bits — `exp + sig` in total, not `1 + exp + sig`. Single precision
is `Float 8 24` and its pattern is 32 bits wide.

Only the Lean side lives here. Turning a float into a term and back is in
`Cvc/{Untyped,Typed}/Term/Float.lean`, beside the constructors that do it.
-/
namespace Cvc public section variable [Ω]

/-- Floats with exponent `exp` and significand `sig`. -/
inductive Float (exp sig : Nat)
/-- Positive infinity. -/
| posInf
/-- Negative infinity. -/
| negInf
/-- Not-a-number. -/
| nan
/-- Zero-right-limit. -/
| posZero
/-- zero-left-limit. -/
| negZero
/-- Bit-pattern representation of a floating point, `exp + sig` bits wide. -/
| ofBitVec (bv : BitVec (exp + sig))
deriving DecidableEq, Hashable, Ord

@[inherit_doc Float.ofBitVec]
def BitVec.toFloat (exp sig : Nat) (bv : BitVec (exp + sig)) : Float exp sig := .ofBitVec bv



namespace Float

instance : ToTyp (Float exp sig) := ⟨.float exp sig⟩

/-- Erased version of `Float`. -/
structure Erased where
  /-- Exponent. -/
  exp : Nat
  /-- Significand. -/
  sig : Nat
  /-- Actual floating-point value. -/
  get : Float exp sig

/-- Erases a floating-point's exponent and significand. -/
def erase (f : Float exp sig) : Erased := {exp, sig, get := f}

/-- String representation.-/
protected def toString (f : Float exp sig) : String :=
  let inner := match f with
  | posInf => "+∞"
  | negInf => "-∞"
  | nan => "NaN"
  | posZero => "+0"
  | negZero => "-0"
  | ofBitVec bv => toString bv
  s!"Float[{exp}, {sig}, {inner}]"

instance : ToString (Float exp sig) := ⟨Float.toString⟩

namespace Erased

@[inherit_doc Float.toString]
protected def toString (f : Erased) := f.get.toString

instance : ToString Erased := ⟨Erased.toString⟩

end Erased

end Float
