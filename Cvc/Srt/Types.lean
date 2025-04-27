/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Srt.Defs



namespace Cvc



/-- Denotes a conversion from the `α` type (not its values) to `Srt`. -/
class ToSrt (α : Type) where private mk ::
  /-- `Srt` version of `α`. -/
  srt : Srt

namespace ToSrt

instance : ToSrt Unit := ⟨.unit⟩
instance : ToSrt Bool := ⟨.bool⟩
instance : ToSrt Int := ⟨.int⟩
instance : ToSrt Rat := ⟨.real⟩
instance : ToSrt String := ⟨.string⟩

/-- Enforces the IEEE 754 standard.

Based on [wikipedia].

[wikipedia]: https://en.wikipedia.org/wiki/Double-precision_floating-point_format#IEEE_754_double-precision_binary_floating-point_format:_binary64
-/
instance : ToSrt Float :=
  ⟨.float 11 53⟩

section variable [A : ToSrt α] [B : ToSrt β]

instance : ToSrt (Array α) := ⟨.seq A.srt⟩
instance : ToSrt (BitVec size) := ⟨.bitVec size⟩
instance : ToSrt (α → β) := ⟨.function A.srt [] B.srt⟩
instance : ToSrt (α × β) := ⟨.prod A.srt B.srt⟩

end

end ToSrt



protected
structure AnyFloat (exp sig : UInt32)

protected
abbrev Float := Cvc.AnyFloat 11 53

namespace AnyFloat

instance : ToSrt (Cvc.AnyFloat exp sig) := ⟨.float exp sig⟩

end AnyFloat



protected
structure Abstract (kind : Srt.Kind)

namespace Abstract

instance : ToSrt (Cvc.Abstract kind) := ⟨.abstract kind⟩

end Abstract



/-- Total map from `Idx` to `Elm`, called *array* in SMT-LIB/cvc. -/
protected
structure TMap (Idx Elm : Type) extends Ord Idx where
mk' ::
  /-- Red-black map representation containing indices with known value. -/
  toRBMap : RBMap Idx Elm
  /-- `Idx → Srt` conversion for user QoL. -/
  IdxToSrt : ToSrt Idx
  /-- `Elm → Srt` conversion for user QoL. -/
  ElmToSrt : ToSrt Elm

namespace TMap  variable [Ord Idx] [I : ToSrt Idx] [E : ToSrt Elm]

/-- Constructor. -/
def ofRBMap (toRBMap : RBMap Idx Elm) : Cvc.TMap Idx Elm :=
  ⟨inferInstance, toRBMap, I, E⟩

/-- A total map with unknown values for all indices. -/
abbrev unspecified : Cvc.TMap Idx Elm :=
  ofRBMap .empty

instance : ToSrt (Cvc.TMap Idx Elm) := ⟨.array I.srt E.srt⟩

end TMap

namespace TMap variable (array : Cvc.TMap Idx Elm)

/-- The known value of an index if any. -/
def get (idx : Idx) : Option Elm :=
  array.toRBMap.find? idx

/-- The known value of an index or a default value. -/
def getD (idx : Idx) (defaultVal : Elm) : Elm :=
  array.get idx |>.getD defaultVal

/-- The known value of an index for `Inhabited` elements. -/
def getI [Inhabited Elm] (idx : Idx) : Elm :=
  array.get idx |>.getD default

instance : GetElem (Cvc.TMap Idx Elm) Idx (Option Elm) (fun _ _ => True) where
  getElem array idx _ := array.get idx

end TMap



/-- Map between elements and their cardinality in the bag. -/
protected
structure Bag (Elm : Type) extends Ord Elm where
mk ::
  /-- Black-tree map representation. -/
  toRBMap : RBMap Elm Nat
  /-- `Elm → Srt` conversion for user QoL. -/
  ElmToSrt : ToSrt Elm

namespace Bag variable [Ord Elm] [E : ToSrt Elm]

/-- Constructor. -/
def ofRBMap (toRBMap : RBMap Elm Nat) : Cvc.Bag Elm :=
  ⟨inferInstance, toRBMap, inferInstance⟩

/-- Empty bag constructor. -/
def empty : Cvc.Bag Elm :=
  ⟨inferInstance, RBMap.empty, inferInstance⟩

instance : ToSrt (Cvc.Bag Elm) := ⟨.bag E.srt⟩

end Bag


namespace Bag variable (bag : Cvc.Bag Elm) (elm : Elm)

/-- Number of distinct elements in the map. -/
def distinctSize : Nat := bag.toRBMap.size

/-- Number of elements in the map, see also `distinctSize`. -/
def size : Nat :=
  0 |> bag.toRBMap.fold fun sum _ n => sum + n

@[inherit_doc size]
def card := @size

/-- Retrieves the multiplicity of an element. -/
def getMult : Nat :=
  bag.toRBMap.find? elm |>.getD 0

/-- True on elements of multiplicity at least one. -/
def contains : Bool :=
  match bag.toRBMap.find? elm with
  | none | some 0 => false
  | some (_ + 1) => true

/-- Removes an element from the bag. -/
def erase : Cvc.Bag Elm :=
  { bag with toRBMap := Lean.RBMap.erase bag.toRBMap elm }

/-- Forces the multiplicity of an element. -/
def setCard : (count : Nat) → Cvc.Bag Elm
| 0 => bag.erase elm
| count =>
  { bag with toRBMap := Lean.RBMap.insert bag.toRBMap elm count}

/-- Passes the multiplicity of an element to a function. -/
def countDo (f : Nat → α) : α :=
  bag.toRBMap.findD elm 0 |> f

/-- Map over the multiplicity of an element. -/
def countMap (f : Nat → Nat) : Cvc.Bag Elm :=
  bag.countDo elm f |> bag.setCard elm

/-- Inserts an element `count` times. -/
def insert (count : Nat := 1) : Cvc.Bag Elm :=
  bag.countMap elm (· + count)

/-- Removes an element `count` times. -/
def remove (count : Nat := 1) : Cvc.Bag Elm :=
  bag.countMap elm (· - count)

end Bag



structure FiniteField (n : Nat)

namespace FiniteField

instance : ToSrt (Cvc.FiniteField n) := ⟨.finiteField n⟩

end FiniteField



structure RoundingMode

namespace RoundingMode

instance : ToSrt Cvc.RoundingMode := ⟨.roundingMode⟩

end RoundingMode



/-- Regular expression. -/
protected
structure Regex where
  /-- String representation. -/
  toString : String

namespace Regex

instance : ToSrt Cvc.Regex := ⟨.regex⟩

end Regex



/-- A set of elements. -/
protected
structure Set (Elm : Type) extends Ord Elm where
mk' ::
  /-- Red-black set representation. -/
  toRBSet : RBSet Elm
  /-- `Elm → Srt` conversion for user QoL. -/
  ElmToSrt : ToSrt Elm

namespace Set variable [Ord Elm] [E : ToSrt Elm]

/-- Constructor. -/
def ofRBSet (toRBSet : RBSet Elm) : Cvc.Set Elm :=
  ⟨inferInstance, toRBSet, inferInstance⟩

/-- Empty set. -/
def empty : Cvc.Set Elm :=
  ofRBSet .empty

instance : ToSrt (Cvc.Set Elm) := ⟨.set E.srt⟩

end Set

namespace Set variable (set : Cvc.Set Elm) (elm : Elm)

/-- Size of the set. -/
def size := set.toRBSet.size

@[inherit_doc size]
def card := @size

/-- True if the element is in the set. -/
def contains : Bool := set.toRBSet.contains elm

/-- Inserts an element in the set. -/
def insert : Cvc.Set Elm :=
  {set with toRBSet := Lean.RBMap.insert set.toRBSet elm ()}

end Set



structure Uninterpreted (cons : Type)

namespace Uninterpreted

instance [A : ToSrt α] : ToSrt (Uninterpreted α) := ⟨.uninterpreted A.srt⟩

end Uninterpreted



namespace Srt

/-- Type corresponding to an `Srt`. -/
abbrev toType : Srt → Type
| .abstract kind => Cvc.Abstract kind
| .array idx elm => Cvc.TMap (toType idx) (toType elm)
| .bag elm => Cvc.Bag (toType elm)
| .bool => Bool
| .bitVec n => BitVec n
| .finiteField n => Cvc.FiniteField n
| .float exp sig => Cvc.AnyFloat exp sig
| .function dom [] cod => toType dom → toType cod
| .function dom (domsHd :: domsTl) cod =>
  toType dom → toType (.function domsHd domsTl cod)
| .int => Int
| .prod lft rgt => lft.toType × rgt.toType
| .real => Rat
| .regex => Cvc.Regex
| .roundingMode => Cvc.RoundingMode
| .seq elm => Array (toType elm)
| .set elm => Cvc.Set (toType elm)
| .string => String
| .unit => Unit
| .uninterpreted cons => Uninterpreted (toType cons)


instance : CoeSort Srt Type := ⟨toType⟩

end Srt


-- namespace Srt

-- class ToType (α : Type) where
--   toType : Srt → Type

-- namespace ToType

-- structure Driver.Builtin

-- namespace Driver.Builtin

-- protected
-- abbrev toType : Srt → Type
-- | .abstract kind => Cvc.Abstract kind
-- | .array idx elm => Cvc.TMap (Builtin.toType idx) (Builtin.toType elm)
-- | .bag elm => Cvc.Bag (Builtin.toType elm)
-- | .bool => Bool
-- | .bitVec n => BitVec n
-- | .finiteField n => Cvc.FiniteField n
-- | .float exp sig => Cvc.AnyFloat exp sig
-- | .function dom [] cod => Builtin.toType dom → Builtin.toType cod
-- | .function dom (domsHd :: domsTl) cod =>
--   Builtin.toType dom → Builtin.toType (.function domsHd domsTl cod)
-- | .int => Int
-- | .real => Rat
-- | .regex => Cvc.Regex
-- | .roundingMode => Cvc.RoundingMode
-- | .seq elm => Array (Builtin.toType elm)
-- | .set elm => Cvc.Set (Builtin.toType elm)
-- | .string => String
-- | .tuple [] => Unit
-- | .tuple [srt] => Builtin.toType srt
-- | .tuple (hd::tl) => Builtin.toType hd × (Builtin.toType <| .tuple tl)
-- | .uninterpreted cons => Uninterpreted (Builtin.toType cons)

-- instance : ToType Builtin := ⟨Builtin.toType⟩

-- end Driver.Builtin

-- end ToType

-- /-- Converts a sort into a type using a `ToType` driver/specification. -/
-- abbrev toTypeUsing (Driver : Type) [T : ToType Driver ] : Srt → Type :=
--   T.toType

-- @[inherit_doc toTypeUsing]
-- abbrev toType {Driver : Type} [T : ToType Driver] : Srt → Type :=
--   T.toType

-- end Srt



class AsSrt (α : Type) extends ToSrt α where
  eq_srt : α = toToSrt.srt := by
    simp only [ToSrt.srt]
    <;> try (unfold Srt.toType)
    <;> try simp -- this is mostly just to trigger `rfl`/`AsSrt.type_eq_srt`

namespace AsSrt

@[simp]
theorem type_eq_srt [A : AsSrt α] : α = A.srt :=
  A.eq_srt

instance : AsSrt Bool := {}
instance : AsSrt Int := {}
instance : AsSrt Rat := {}
instance : AsSrt Cvc.Regex := {}
instance : AsSrt String := {}
instance : AsSrt Cvc.RoundingMode := {}
instance : AsSrt (Cvc.FiniteField size) := {}
instance : AsSrt (BitVec size) := {}
instance : AsSrt (Cvc.AnyFloat exp sig) := {}

instance [AsSrt cons] : AsSrt (Cvc.Uninterpreted cons) := {}
instance [AsSrt α] : AsSrt (Cvc.Bag α) := {}
instance [AsSrt α] : AsSrt (Array α) := {}
instance [AsSrt α] : AsSrt (Cvc.Set α) := {}
instance [AsSrt Idx] [AsSrt Elm] : AsSrt (Cvc.TMap Idx Elm) := {}
-- instance [AsSrt Idx] [AsSrt Elm] : AsSrt (Cvc.TMap Idx Elm) := {}

end AsSrt
