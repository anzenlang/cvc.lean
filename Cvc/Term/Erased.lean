/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Defs



namespace Cvc



/-- Type-erased version `Term`. -/
structure ETerm where
/-- Constructor from a typed-term. -/
mk ::
  /-- Sort of the underlying typed-term. -/
  srt : Srt
  /-- Typed version of a type-erased term. -/
  typed : Term srt.toType

/-- An erased value for some `Srt`. -/
structure EValue where
/-- Constructor. -/
mk ::
  /-- Sort of the value. -/
  srt : Srt
  /-- Underlying typed value as a `Term`. -/
  val : Term srt.toType



namespace ETerm

/-- Constructor from a typed term. -/
def ofTerm {α : Type} [A : Srt.Bij α] (term : Term α) : ETerm :=
  mk A.srt (A.h_bij ▸ term)

section variable (erased : ETerm)

/-- String representation. -/
protected def toString : String := toString erased.typed

instance : ToString ETerm := ⟨ETerm.toString⟩

/-- Attempts to `Srt`-type an erased term. -/
def asSrt? (srt : Srt) : Option (Term srt.toType) :=
  let ⟨termSrt, term⟩ := erased
  if h_srt : termSrt = srt then some (h_srt ▸ term) else none

/-- Attempts to `Srt`-type an erased term. -/
def asSrt (srt : Srt) : Res (Term srt.toType) :=
  if let some term := erased.asSrt? srt then .ok term
  else Error.throwUser s!"erased term of type `{erased.srt}` cannot be typed as `{srt}`"

/-- Attempts to retype an erased term. -/
def as? (α : Type) [A : Srt.Bij α] : Option (Term α) := by
  cases A ; case mk srt h_bij =>
  cases h_bij
  exact erased.asSrt? srt

/-- Attempts to retype an erased term. -/
def as (α : Type) [A : Srt.Bij α] : Res (Term α) :=
  if let some term := erased.as? α then return term
  else Error.throwUser s!"erased term of type `{erased.srt}` cannot be typed as `{A.srt}`"

/-- Retrieve the erased value of an erased term. -/
def getValue : Smt.Sat EValue := do
  let ⟨srt, term⟩ := erased
  let val ← Smt.getValue term
  return ⟨srt, val⟩

end

end ETerm

namespace Term

/-- Erases the type of a typed term. -/
def erase [Srt.Bij α] : Term α → ETerm := .ofTerm

@[inherit_doc ETerm.as?]
def ofErased? [A : Srt.Bij α] (erased : ETerm) : Option (Term α) :=
  erased.as? α

@[inherit_doc ETerm.as]
def ofErased [A : Srt.Bij α] (erased : ETerm) : Res (Term α) :=
  erased.as α

end Term
