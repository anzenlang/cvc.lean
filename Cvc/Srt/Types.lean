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

instance : ToSrt Unit := ⟨.tuple #[]⟩
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

instance [ToSrt α] : ToSrt (Array α) := ⟨.seq <| srt α⟩
instance : ToSrt (BitVec size) := ⟨.bitVec size⟩

end ToSrt



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

namespace TMap  variable [Ord Idx] [ToSrt Idx] [ToSrt Elm]

/-- Constructor. -/
def ofRBMap [o : Ord Idx] [i : ToSrt Idx] [e : ToSrt Elm]
  (toRBMap : RBMap Idx Elm)
: Cvc.TMap Idx Elm :=
  ⟨o, toRBMap, i, e⟩

/-- A total map with unknown values for all indices. -/
abbrev unspecified : Cvc.TMap Idx Elm :=
  ofRBMap .empty

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



/-- A set of elements. -/
protected
structure Set (Elm : Type) extends Ord Elm where
mk' ::
  /-- Red-black set representation. -/
  toRBSet : RBSet Elm
  /-- `Elm → Srt` conversion for user QoL. -/
  ElmToSrt : ToSrt Elm

namespace Set variable [Ord Elm] [ToSrt Elm]

/-- Constructor. -/
def ofRBSet (toRBSet : RBSet Elm) : Cvc.Set Elm :=
  ⟨inferInstance, toRBSet, inferInstance⟩

/-- Empty set. -/
def empty : Cvc.Set Elm :=
  ofRBSet .empty

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



/-- Regular expression. -/
protected
structure Regex where
  /-- String representation. -/
  toString : String



namespace ToSrt

variable [A : ToSrt α] [B : ToSrt β]

/-- Conversion from maps ("arrays" in SMT-LIB) to sort. -/
instance : ToSrt (Cvc.TMap α β) := ⟨.array A.srt B.srt⟩
instance : ToSrt (Cvc.Bag α) := ⟨.bag A.srt⟩
instance : ToSrt (α → β) := ⟨.function #[] A.srt B.srt⟩
-- instance : ToSrt Regex := ⟨.regex⟩
instance : ToSrt (Cvc.Set α) := ⟨.set A.srt⟩
instance : ToSrt (α × β) := ⟨.tuple #[A.srt, B.srt]⟩

end ToSrt
