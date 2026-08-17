/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt
public import Std.Data.TreeSet.Basic
public import Std.Data.TreeSet.Iterator



/-! # Sets

The Lean type denoting an SMT set. It is a `Std.TreeSet`, so its element type must be ordered —
which is where the `Ord` binders on the generated set operators come from.

Only the Lean side lives here. Turning a set into a term and back is in
`Cvc/{Untyped,Typed}/Term/Set.lean`, beside the constructors that do it.
-/
namespace Cvc public section variable [Ω]

/-- Alias for `Std.TreeSet`. -/
abbrev Set (α : Type) [Ord α] := Std.TreeSet α

namespace Set variable [Ord α]

open Std renaming TreeSet → S

@[inherit_doc S.empty] def empty : Set α := S.empty
@[inherit_doc S.ofArray] def ofArray := S.ofArray (α := α)

instance [A : ToTyp α] : ToTyp (Set α) := ⟨.set A.typ⟩

/-- String representation. -/
protected def toString [ToString α] (set : Set α) : String :=
  if set.isEmpty then "∅" else Id.run do
    let mut s := ""
    let mut sep := ""
    for elem in set do
      s := s!"{s}{sep}{elem}"
      sep := ", "
    s!"\{ {s} }"

instance [ToString α] : ToString (Set α) := ⟨Set.toString⟩

protected def compare (s1 s2 : Set α) : Ordering := Id.run do
  let mut s2 := s2.iter
  for val1 in s1 do
    let some (s2', val2) := getNext s2
      | return .gt
    match compare val1 val2 with | .eq => pure () | cmp => return cmp
    s2 := s2'
  if s2.isEmpty then .eq else .lt
where
  getNext (it : Std.Iter α) : Option (Std.Iter α × α) :=
    match it.step with
    | ⟨.yield it' val, _⟩ => some (it', val)
    | ⟨.done, _⟩ => none
    | ⟨.skip it', _⟩ => getNext it'
  termination_by it.finitelyManySkips

instance : Ord (Set α) := ⟨Set.compare⟩

/--
info: compare ∅ ∅
→ Ordering.eq

compare { 5 } { 5 }
→ Ordering.eq
compare { 5 } ∅
→ Ordering.gt
compare ∅ { 5 }
→ Ordering.lt

compare { 3 } { 3 }
→ Ordering.eq
compare { 3 } { 5 }
→ Ordering.lt
compare { 5 } { 3 }
→ Ordering.gt

compare { 3, 7 } { 3, 7 }
→ Ordering.eq
compare { 3, 7 } { 5 }
→ Ordering.lt
compare { 5 } { 3, 7 }
→ Ordering.gt
compare { 3, 7 } { 3 }
→ Ordering.gt
compare { 3 } { 3, 7 }
→ Ordering.lt
-/
#guard_msgs in #eval do
  let showCmp (b1 b2 : Set Nat) :=
    println! "compare {b1} {b2}\n→ {b1.compare b2 |> repr}"
  let set := Set.empty
  showCmp set set
  println! ""
  let set1 := set.insert 5
  showCmp set1 set1
  showCmp set1 set
  showCmp set set1
  println! ""
  let set2 := set.insert 3
  showCmp set2 set2
  showCmp set2 set1
  showCmp set1 set2
  println! ""
  let set3 := set2.insert 7
  showCmp set3 set3
  showCmp set3 set1
  showCmp set1 set3
  showCmp set3 set2
  showCmp set2 set3

end Set
