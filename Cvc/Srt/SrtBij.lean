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

@[inherit_doc getSrt]
abbrev ofType := Cvc.getSrt

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

/-! ## Instances composite types -/
section variable [A : Srt.Bij α] [B : Srt.Bij β]

instance instArray : Srt.Bij (Array α) := mk <| .seq A.srt
instance instBitVec : Srt.Bij (BitVec size) := mk <| .bitVec size
instance instFunction : Srt.Bij (α → β) := mk <| .function A.srt B.srt
instance instProd : Srt.Bij (α × β) := mk <| .prod A.srt B.srt
instance instTMap : Srt.Bij (Cvc.TMap α β) := mk <| .array A.srt B.srt
instance instBag : Srt.Bij (Cvc.Bag α) := mk <| .bag A.srt
instance instSet : Srt.Bij (Cvc.Set α) := mk <| .set A.srt
instance instUninterpreted : Srt.Bij (Uninterpreted α) := mk <| .uninterpreted A.srt

end

end Bij
end Srt



/-! ## Refinement of `Srt.Bij` to arithmetic sorts -/

/-- Proof that the sort associated to `α` is arithmetic. -/
protected abbrev is_arith (α : Type) [Srt.Bij α] :=
  Srt.ofType α |>.is_arith

namespace Srt.Bij

/-- Extends `Srt.Bij` with a proof that `α`'s `Srt` is arithmetic. -/
protected class Arith (α : Type) extends Srt.Bij α where
  /-- Sort `srt` is an arithmetic sort. -/
  h_arith : Cvc.is_arith α := by simp

namespace Arith

example [Srt.Bij.Arith α] : Srt.Bij α := inferInstance

/-! ## Instances for `Int` and `Rat` (`Real`) -/
instance instInt : Bij.Arith Int := {}
instance instRat : Bij.Arith Rat := {}

end Arith

end Srt.Bij
