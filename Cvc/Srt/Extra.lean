/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Srt.Defs
import Cvc.Srt.Types



/-! # Relates `Srt`-s to `Type`-s

Main class `IsSrt (α : Type)` associates `srt : Srt` to `α`. It guarantees this association works
both ways by asking for a proof that `α = srt.toType`.
-/
namespace Cvc



/-- Provides a `srt : Srt` such that `α = srt.toType`. -/
class IsSrt (α : Type) where mk ::
  /-- `Srt` version of `α`. -/
  srt : Srt
  /-- Turning `srt` into a `Type` results in `α`. -/
  h_bij : α = srt := by
    simp [Cvc.Srt.toType, IsSrt.h_bij, *] <;> rfl

/-- Retrieves the `Srt` corresponding to a `Type`. -/
abbrev getSrt (α : Type) [I : IsSrt α] : Srt :=
  I.srt

namespace Srt

instance instIsSrt (srt : Srt) : IsSrt srt := { srt }

@[inherit_doc getSrt]
abbrev ofType := Cvc.getSrt

@[simp]
theorem toType_ofType (α : Type) [I : IsSrt α] : ofType α = α := by
  let {srt, h_bij} := I
  cases h_bij
  cases srt <;> rfl

@[simp]
theorem ofType_toType (srt : Srt) : ofType srt = srt := by
  cases srt <;> rfl

end Srt

namespace IsSrt

/-! ## Instances for simple types -/

instance instUnit : IsSrt Unit := mk .unit
instance instBool : IsSrt Bool := mk .bool
instance instInt : IsSrt Int := mk .int
instance instRat : IsSrt Rat := mk .real
instance instString : IsSrt String := mk .string
instance instRoundingMode : IsSrt Cvc.RoundingMode := mk <| .roundingMode
instance instRegex : IsSrt Cvc.Regex := mk <| .regex

/-! ## Instances for non-`Srt`-parameterized types -/
instance instAnyFloat : IsSrt (Cvc.AnyFloat exp sig) := mk <| .float exp sig
instance instAbstract : IsSrt (Cvc.Abstract k) := mk <| .abstract k
instance instFiniteField : IsSrt (Cvc.FiniteField n) := mk <| .finiteField n
instance instBitVec : IsSrt (BitVec size) := mk <| .bitVec size
instance instUninterpreted : IsSrt (Uninterpreted name) := mk <| .uninterpreted name

/-! ## Instances composite types -/
section variable [A : IsSrt α] [B : IsSrt β]

instance instArray : IsSrt (Array α) := mk <| .seq A.srt
instance instFunction : IsSrt (α → β) := mk <| .function A.srt B.srt
instance instProd : IsSrt (α × β) := mk <| .prod A.srt B.srt
instance instTMap : IsSrt (Cvc.TMap α β) := mk <| .array A.srt B.srt
instance instBag : IsSrt (Cvc.Bag α) := mk <| .bag A.srt
instance instSet : IsSrt (Cvc.Set α) := mk <| .set A.srt

end

end IsSrt



/-! ## Refinement of `IsSrt` to arithmetic sorts -/

/-- Proof that the sort associated to `α` is arithmetic. -/
protected abbrev is_arith (α : Type) [IsSrt α] :=
  Srt.ofType α |>.is_arith

instance [IsSrt α] : Decidable (Cvc.is_arith α) := by
  simp only [Cvc.is_arith, Srt.is_arith, Srt.isArith, Srt.ofType, getSrt]
  cases IsSrt.srt α <;> (
    simp
    try exact instDecidableFalse
    try exact instDecidableTrue
  )

@[simp]
theorem is_arith_def (α : Type) [inst : IsSrt α] : Cvc.is_arith α → (α = Int ∨ α = Rat) := by
  let {srt, h_bij} := inst
  cases h_bij
  cases srt <;> simp

def is_arith_srt_def (α : Type) [inst : IsSrt α]
: Cvc.is_arith α → (inst.srt = .int ∨ inst.srt = .real) := by
  let {srt, h_bij} := inst
  cases h_bij
  cases srt <;> simp

namespace IsSrt

/-- Extends `IsSrt` with a proof that `α`'s `Srt` is arithmetic. -/
protected class Arith (α : Type) extends toIsSrt : IsSrt α where
  /-- Sort `srt` is an arithmetic sort. -/
  h_arith : Cvc.is_arith α := by simp

namespace Arith

example [IsSrt.Arith α] : IsSrt α := inferInstance

/-! ## Instances for `Int` and `Rat` (`Real`) -/
instance instInt : IsSrt.Arith Int := {}
instance instRat : IsSrt.Arith Rat := {}

theorem int_or_rat (α : Type) [inst : IsSrt.Arith α] : α = Int ∨ α = Rat :=
  Cvc.is_arith_def α inst.h_arith

def int_or_rat' (α : Type) [inst : IsSrt.Arith α] : inst.srt = .int ∨ inst.srt = .real :=
  Cvc.is_arith_srt_def α inst.h_arith

def inspect' (α : Type) [inst : IsSrt.Arith α]
  (fInt : (h : α = Int) → β) (fRat : (h : α = Rat) → β)
: β :=
  let { toIsSrt, h_arith } := inst
  let { srt, h_bij } := toIsSrt
  by
    cases inst.int_or_rat
    case inl => apply fInt ; assumption
    case inr => apply fRat ; assumption

def inspect {α : Type} {β : Sort u} [inst : IsSrt.Arith α]
  (fInt : (h : inst.srt = .int) → β) (fRat : (h : inst.srt = .real) → β)
: β :=
  inst.int_or_rat'.by_cases fInt fRat

end Arith

end IsSrt
