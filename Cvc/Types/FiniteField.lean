/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt



/-! # Finite-field elements

The Lean type denoting a value of SMT sort `(_ FiniteField size)`, held as the integer representing
it. cvc5 answers in the *symmetric* representation, so an element of `GF(5)` comes back in
`[-2, 2]` rather than `[0, 4]`: `3` reads back as `-2`.

Only the Lean side lives here. Turning an element into a term and back is in
`Cvc/{Untyped,Typed}/Term/FiniteField.lean`, beside the constructors that do it.
-/
namespace Cvc public section variable [Ω]

/-- An element of a finite field of size `size`. -/
structure FiniteField (size : Nat) where
  /-- Element representation. -/
  repr : Int
deriving DecidableEq, Hashable, Ord

namespace FiniteField

instance : ToTyp (FiniteField size) := ⟨.finiteField size⟩

/-- Erased version of `FiniteField`. -/
structure Erased where
  /-- The field's size. -/
  size : Nat
  /-- The actual finite field element. -/
  get : FiniteField size

/-- Erases a finite-field-element's size. -/
def erase (elem : FiniteField size) : Erased := {size, get := elem}

/-- String representation. -/
protected def toString (ff : FiniteField size) : String := toString ff.repr

instance : ToString (FiniteField size) := ⟨FiniteField.toString⟩

namespace Erased

@[inherit_doc FiniteField.toString]
protected def toString (elem : Erased) := elem.get.toString

instance : ToString Erased := ⟨Erased.toString⟩

end Erased

end FiniteField
