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
public import Std.Data.TreeMap.Iterator



/-! # Bags

The Lean type denoting an SMT bag: a `Std.TreeMap` from elements to their multiplicity, so the
element type must be ordered. A zero multiplicity is not represented, which is what `alter` keeps
true.

Only the Lean side lives here. Turning a bag into a term and back is in
`Cvc/{Untyped,Typed}/Term/Bag.lean`, beside the constructors that do it.
-/
namespace Cvc public section variable [Ω]

abbrev Bag (α : Type) [Ord α] := Std.TreeMap α Int

namespace Bag variable [Ord α] (bag : Bag α)

def empty : Bag α := Std.TreeMap.empty

def alter (key : α) (f : Int → Int) : Bag α :=
  Std.TreeMap.alter bag key fun val? => match val?.getD 0 |> f with | 0 => none | n => n

def increment (key : α) := bag.alter key (· + 1)

def decrement (key : α) := bag.alter key (· - 1)

def add (key : α) (n : Int) := bag.alter key (· + n)

def sub (key : α) (n : Int) := bag.alter key (· - n)

def get? (key : α) : Option Int := Std.TreeMap.get? bag key

def get (key : α) : Int := bag.get? key |>.getD 0

def contains (key : α) : Bool := 0 < bag.get key

protected abbrev mem (key : α) : Prop := bag.contains key

instance : Membership α (Bag α) := ⟨Bag.mem⟩

omit [Ω] in
theorem mem_def {key : α} : (key ∈ bag) = bag.contains key := rfl

instance (key : α) : Decidable (key ∈ bag) :=
  bag.mem_def ▸ if h : bag.contains key then isTrue h else isFalse h

protected def toString [ToString α] (bag : Bag α) : String :=
  if bag.isEmpty then "∅" else
  let inner :=
    bag.foldl (init := "") fun
      | acc, _key, 0 => acc
      | acc, key, n => s!"{if acc.isEmpty then acc else acc ++ ", "}{key} ↦ {n}"
  s!"\{ {inner} }"

instance [ToString α] : ToString (Bag α) := ⟨Bag.toString⟩

instance [A : ToTyp α] : ToTyp (Bag α) := ⟨.bag A.typ⟩

protected def compare (b1 b2 : Bag α) : Ordering := Id.run do
  let mut b2 := b2.iter
  for (key, val) in b1 do
    let some (b2', key', val') := getNext b2
      | return .gt
    match compare key key' with | .eq => pure () | cmp => return cmp
    match compare val val' with | .eq => pure () | cmp => return cmp
    b2 := b2'
  if b2.isEmpty then .eq else .lt
where
  getNext (it : Std.Iter (α × Int)) : Option (Std.Iter (α × Int) × α × Int) :=
    match it.step with
    | ⟨.yield it' (key, val), _⟩ => some (it', key, val)
    | ⟨.done, _⟩ => none
    | ⟨.skip it', _⟩ => getNext it'
  termination_by it.finitelyManySkips

instance : Ord (Bag α) := ⟨Bag.compare⟩

/--
info: compare ∅ ∅
→ Ordering.eq

compare { 5 ↦ 2 } { 5 ↦ 2 }
→ Ordering.eq
compare { 5 ↦ 2 } ∅
→ Ordering.gt
compare ∅ { 5 ↦ 2 }
→ Ordering.lt

compare { 5 ↦ 1 } { 5 ↦ 1 }
→ Ordering.eq
compare { 5 ↦ 1 } { 5 ↦ 2 }
→ Ordering.lt
compare { 5 ↦ 2 } { 5 ↦ 1 }
→ Ordering.gt

compare { 5 ↦ 1, 7 ↦ 3 } { 5 ↦ 1, 7 ↦ 3 }
→ Ordering.eq
compare { 5 ↦ 1, 7 ↦ 3 } { 5 ↦ 2 }
→ Ordering.lt
compare { 5 ↦ 2 } { 5 ↦ 1, 7 ↦ 3 }
→ Ordering.gt
compare { 5 ↦ 1, 7 ↦ 3 } { 5 ↦ 1 }
→ Ordering.gt
compare { 5 ↦ 1 } { 5 ↦ 1, 7 ↦ 3 }
→ Ordering.lt
-/
#guard_msgs in #eval do
  let showCmp (b1 b2 : Bag Nat) :=
    println! "compare {b1} {b2}\n→ {b1.compare b2 |> repr}"
  let bag := Bag.empty
  showCmp bag bag
  println! ""
  let bag1 := bag.insert 5 2
  showCmp bag1 bag1
  showCmp bag1 bag
  showCmp bag bag1
  println! ""
  let bag2 := bag.insert 5 1
  showCmp bag2 bag2
  showCmp bag2 bag1
  showCmp bag1 bag2
  println! ""
  let bag3 := bag2.insert 7 3
  showCmp bag3 bag3
  showCmp bag3 bag1
  showCmp bag1 bag3
  showCmp bag3 bag2
  showCmp bag2 bag3

end Bag
