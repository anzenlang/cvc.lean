/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Srt.Defs
import Cvc.Srt.Types



/-! # Relates `Srt`-s to `Type`-s

Main class `Srt.Bij (α : Type)` associates `srt : Srt` to `α`. It guarantees this association works
both ways by asking for a proof that `α = srt.toType`.
-/
namespace Cvc



/-- Denotes a *"bijection"* from the `α` type itself (not its values) to `Srt`.

*"Bijection"* here means that when `A : SrtBij α`, then `A.srt.toType = α` as guaranteed by `valid`.
-/
protected class Srt.Bij (α : Type) where private mk ::
  /-- `Srt` version of `α`. -/
  srt : Srt
  /-- Turning `srt` into a `Type` results in `α`. -/
  h_bij : α = srt.toType := by
    simp [toType, Srt.Bij.h_bij, *] <;> rfl

/-- Retrieves the `Srt` corresponding to a `Type`. -/
abbrev getSrt (α : Type) [I : Srt.Bij α] : Srt :=
  I.srt

namespace Srt

instance toBijType (srt : Srt) : Srt.Bij srt.toType where
  srt

@[inherit_doc getSrt]
abbrev ofType := Cvc.getSrt

@[simp]
theorem toType_ofType (α : Type) [I : Srt.Bij α] : (ofType α).toType = α := by
  let {srt, h_bij} := I
  cases h_bij
  cases srt <;> rfl

@[simp]
theorem ofType_toType (srt : Srt) : ofType (srt.toType) = srt := by
  cases srt <;> rfl

namespace Bij

/-! ## Instances for simple types -/

instance instUnit : Srt.Bij Unit := mk .unit
instance instBool : Srt.Bij Bool := mk .bool
instance instInt : Srt.Bij Int := mk .int
instance instRat : Srt.Bij Rat := mk .real
instance instString : Srt.Bij String := mk .string
instance instRoundingMode : Srt.Bij Cvc.RoundingMode := mk <| .roundingMode
instance instRegex : Srt.Bij Cvc.Regex := mk <| .regex

/-! ## Instances for non-`Srt`-parameterized types -/
instance instAnyFloat : Srt.Bij (Cvc.AnyFloat exp sig) := mk <| .float exp sig
instance instAbstract : Srt.Bij (Cvc.Abstract k) := mk <| .abstract k
instance instFiniteField : Srt.Bij (Cvc.FiniteField n) := mk <| .finiteField n
instance instBitVec : Srt.Bij (BitVec size) := mk <| .bitVec size
instance instUninterpreted : Srt.Bij (Uninterpreted name) := mk <| .uninterpreted name

/-! ## Instances composite types -/
section variable [A : Srt.Bij α] [B : Srt.Bij β]

instance instArray : Srt.Bij (Array α) := mk <| .seq A.srt
instance instFunction : Srt.Bij (α → β) := mk <| .function A.srt B.srt
instance instProd : Srt.Bij (α × β) := mk <| .prod A.srt B.srt
instance instTMap : Srt.Bij (Cvc.TMap α β) := mk <| .array A.srt B.srt
instance instBag : Srt.Bij (Cvc.Bag α) := mk <| .bag A.srt
instance instSet : Srt.Bij (Cvc.Set α) := mk <| .set A.srt

end

end Bij
end Srt



/-! ## Refinement of `Srt.Bij` to arithmetic sorts -/

/-- Proof that the sort associated to `α` is arithmetic. -/
protected abbrev is_arith (α : Type) [Srt.Bij α] :=
  Srt.ofType α |>.is_arith

instance [Srt.Bij α] : Decidable (Cvc.is_arith α) := by
  simp only [Cvc.is_arith, Srt.is_arith, Srt.isArith, Srt.ofType, getSrt]
  cases Srt.Bij.srt α <;> (
    simp
    try exact instDecidableFalse
    try exact instDecidableTrue
  )

@[simp]
theorem is_arith_def (α : Type) [inst : Srt.Bij α] : Cvc.is_arith α → (α = Int ∨ α = Rat) := by
  let {srt, h_bij} := inst
  cases h_bij
  cases srt <;> simp

def is_arith_srt_def (α : Type) [inst : Srt.Bij α]
: Cvc.is_arith α → (inst.srt = .int ∨ inst.srt = .real) := by
  let {srt, h_bij} := inst
  cases h_bij
  cases srt <;> simp

namespace Srt
namespace Bij



/-- Extends `Srt.Bij` with a proof that `α`'s `Srt` is arithmetic. -/
protected class Arith (α : Type) extends Srt.Bij α where
  /-- Sort `srt` is an arithmetic sort. -/
  h_arith : Cvc.is_arith α := by simp

namespace Arith

example [Srt.Bij.Arith α] : Srt.Bij α := inferInstance

/-! ## Instances for `Int` and `Rat` (`Real`) -/
instance instInt : Bij.Arith Int := {}
instance instRat : Bij.Arith Rat := {}

theorem int_or_rat (α : Type) [inst : Srt.Bij.Arith α] : α = Int ∨ α = Rat :=
  Cvc.is_arith_def α inst.h_arith

def int_or_rat' (α : Type) [inst : Srt.Bij.Arith α] : inst.srt = .int ∨ inst.srt = .real :=
  Cvc.is_arith_srt_def α inst.h_arith

def inspect' (α : Type) [inst : Srt.Bij.Arith α]
  (fInt : (h : α = Int) → β) (fRat : (h : α = Rat) → β)
: β :=
  let { toBij, h_arith } := inst
  let { srt, h_bij } := toBij
  by
    cases inst.int_or_rat
    case inl => apply fInt ; assumption
    case inr => apply fRat ; assumption

def inspect {α : Type} {β : Sort u} [inst : Srt.Bij.Arith α]
  (fInt : (h : inst.srt = .int) → β) (fRat : (h : inst.srt = .real) → β)
: β :=
  inst.int_or_rat'.by_cases fInt fRat

end Arith

end Bij

end Srt
