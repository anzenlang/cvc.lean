/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt
public import Std.Data.TreeMap.Basic



/-! # Arrays

The Lean type denoting an SMT array: a default element plus the finitely many indices that differ
from it. Indices are held in a `Std.TreeMap`, so the index type must be ordered.

Only the Lean side lives here. Turning a total map into a term and back is in
`Cvc/{Untyped,Typed}/Term/Array.lean`, beside the constructors that do it.
-/
namespace Cvc public section variable [Ω]

/-- A total map from `α` (the indices) to `β` (the elements), used to encode SMT-LIB arrays. -/
structure TotalMap (α β : Type) [Ord α] where
  /-- Default element that all indices not captured by `map` are mapped to. -/
  defaultElem : β
  /-- Maps indices to elements. -/
  map : Std.TreeMap α β := Std.TreeMap.empty

namespace TotalMap variable [Ord α]

def mkConst (defaultElem : β) : TotalMap α β where defaultElem

protected def default [Inhabited β] : TotalMap α β := mkConst default
instance [B : Nonempty β] : Nonempty (TotalMap α β) := B.elim (⟨· , Std.TreeMap.empty⟩)
instance [Inhabited β] : Inhabited (TotalMap α β) := ⟨TotalMap.default⟩

instance [ToTyp α] [ToTyp β] : ToTyp (TotalMap α β) := ⟨Typ.of α |>.arrayTo (Typ.of β)⟩

/-! #### Basic operations -/
section variable [Ord α] (map : TotalMap α β) (key : α)

def insert (val : β) : TotalMap α β :=
  {map with map := map.map.insert key val}

def get? : Option β := map.map.get? key

def get : β := map.get? key |>.getD map.defaultElem

end

/-! #### String representation -/

section variable [ToString α] [ToString β] (map : TotalMap α β)

def foldlStrings (f : γ → Bool → String → γ) (init : γ) : γ := Id.run do
  let mut acc := init
  for (key, val) in map.map do
    acc := f acc false s!"{key} ↦ {val}"
  f acc true s!"_ ↦ {map.defaultElem}"

def lines : Array String := map.foldlStrings (init := #[]) fun acc _ s => acc.push s

/-- String representation. -/
protected def toString : String := Id.run do
  map.foldlStrings (init := "{ ") fun acc isLast line =>
    s!"{acc}{line}{if isLast then " }" else ", "}"

instance : ToString (TotalMap α β) := ⟨TotalMap.toString⟩

end

end TotalMap
