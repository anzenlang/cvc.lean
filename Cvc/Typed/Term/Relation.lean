/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Term.Defs
import all Cvc.Typed.Term.Defs
-- `Col`/`Cols` hold their positions privately, and the projections below are what read them out
import all Cvc.Types.Relation

public import Cvc.Types.Relation
public import Cvc.Untyped.Term.Relation
public import Cvc.Typed.Term.Defs
public import Cvc.Typed.Term.Set
public import Cvc.Typed.Term.Arith



/-! # Relations, typed

A relation is indexed by `Rel α β` — a set of tuples whose components are `α ++ [β]`. See
`Types/Relation.lean` for why the last component is split off; in short, it makes "drop the last
component" something unification can do, which is what lets `relJoin` be a signature rather than a
type-level program.

**The set operators are restated here rather than reached through `Set`**, so working with a
relation never means leaving the relation world. `relUnion`, `relMember` and the rest are the set
operators at a relation's index; `relToSet` is there for the two that genuinely leave it, `setMap`
and `setFold`, whose results are arbitrary sets.

cvc5 marks every relation-specific kind experimental.
-/
namespace Cvc.Typed.Term public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## Tuples -/

/-- The components of a tuple, in order, along with the index they denote.

`last` and `cons` are the only builders, so the number of terms and the number of components the
index describes stay in step.
-/
structure Tup.Components (α : List Type) (β : Type) where
  private mk ::
  private terms : Untyped.Terms

namespace Tup.Components

/-- The final component. -/
def last (component : Term β) : Tup.Components [] β := ⟨#[component.erase]⟩

/-- Adds a component in front of the ones collected so far. -/
def cons (component : Term α) (rest : Tup.Components αs β) : Tup.Components (α :: αs) β :=
  ⟨#[component.erase] ++ rest.terms⟩

end Tup.Components

/-- The tuple whose components are the given ones.

A component that is itself a tuple stays one: `Tup [α] (Tup [β] γ)` denotes
`(Tuple α (Tuple β γ))`, not a three-component tuple.
-/
def mkTup (components : Tup.Components α β) : Env (Term (Tup α β)) :=
  T.mkTuple components.terms

/-! Reading a tuple back apart. The index is a list, so each of these is a component position that
unification or `List.length` can compute — no type-level program is needed, unlike the product
index where a middle component has no accessor at all.
-/

/-- The first component.

`α :: αs` is a constructor pattern, so the position is `0` whatever follows.
-/
def tupFst (tuple : Term (Tup (α :: αs) β)) : Env (Term α) :=
  tuple.erase.tupleSelect 0

/-- The last component.

Its position is the length of `α`, which computes: a `List Type` is an ordinary runtime value, so
this works at any arity without the index having to be concrete.
-/
def tupLast (tuple : Term (Tup α β)) : Env (Term β) :=
  tuple.erase.tupleSelect α.length

/-- Every component but the first, as a tuple.

A projection rather than a selection, since the result has more than one component in general.
Composing it with `tupFst` reaches any position.
-/
def tupRest (tuple : Term (Tup (α :: αs) β)) : Env (Term (Tup αs β)) :=
  -- components `1 … αs.length + 1`: all of `αs`, then `β`
  tuple.erase.tupleProject ((Array.range (αs.length + 1)).map (· + 1))

/-- The component at the given position, at that component's own type.

The general form of `tupFst`/`tupLast`, and the way to reach a middle component without composing
`tupRest`: `t.tupAt col%1` is the second one.
-/
def tupAt (tuple : Term (Tup α β)) (idx : Col α β γ) : Env (Term γ) :=
  tuple.erase.tupleSelect idx.toNat

/-- The tuple of the components at the given positions, in the order given.

A tuple-to-tuple operation, as `tupleSelect` is not: projecting one position gives a one-component
tuple, where `tupAt` gives the component. The `Cols` spine is what carries the result's index, so
this is typed where the sort-erased `Untyped.Term.tupleProject` cannot be.
-/
def tupProject (cols : Cols α β α' β') (tuple : Term (Tup α β)) : Env (Term (Tup α' β')) :=
  tuple.erase.tupleProject cols.toArray



/-! ## Crossing to and from sets

Both directions are the identity on terms: a relation *is* a set of tuples, and only the index
differs. They are here for the operators that leave the relation world, and for interoperating with
code written against `Set`.
-/

/-- Reads a relation as the set of tuples it is. -/
def relToSet [Ord (Tup α β)] (rel : Term (Rel α β)) : Term (Set (Tup α β)) := rel

/-- Reads a set of tuples as the relation it is. -/
def relOfSet [Ord (Tup α β)] (set : Term (Set (Tup α β))) : Term (Rel α β) := set



/-! ## Relational operators -/

/-- Composition: `lft`'s last component and `rgt`'s first are the same `mu`, and both are dropped.

The shared `mu` is cvc5's joinability requirement, stated in the signature rather than checked at
run time.
-/
def relJoin (lft : Term (Rel α μ)) (rgt : Term (Rel (μ :: α') β'))
: Env (Term (Rel (α ++ α') β')) :=
  T.relJoin lft.erase rgt.erase

/-- Cartesian product: every pairing, with the components appended. -/
def relProduct (lft : Term (Rel α β)) (rgt : Term (Rel α' β'))
: Env (Term (Rel (α ++ β :: α') β')) :=
  T.relProduct lft.erase rgt.erase

/-- The components of a transposed relation: the whole list, reversed. -/
abbrev transposed : (α : List Type) → (β : Type) → Type
  | [], β => Rel [] β
  | hd :: tl, β => Rel (β :: tl.reverse) hd

/-- Reverses every tuple's components. -/
def relTranspose (rel : Term (Rel α β)) : Env (Term (transposed α β)) :=
  T.relTranspose rel.erase

/-- Transitive closure of a homogeneous binary relation. -/
def relTclosure (rel : Term (Rel [α] α)) : Env (Term (Rel [α] α)) :=
  T.relTclosure rel.erase

/-- The identity relation over a unary relation's elements.

`Rel [] α` *is* the unary relation — the split index says so directly, with no separate
one-component tuple type needed.
-/
def relIden (rel : Term (Rel [] α)) : Env (Term (Rel [α] α)) :=
  T.relIden rel.erase

/-- The elements of a binary relation related to at least `size` others. -/
def relJoinImage (rel : Term (Rel [α] β)) (size : Term Int) : Env (Term (Rel [] α)) :=
  T.relJoinImage rel.erase size.erase

/-- Partitions the relation, putting tuples that agree on the given components in the same part.

Answers a set *of relations*. The indices choose what is compared and so do not reach the result's
sort.
-/
def relGroup [Ord (Rel α β)] (indices : Array Nat) (rel : Term (Rel α β))
: Env (Term (Set (Rel α β))) :=
  T.relGroup indices rel.erase

/-- Folds each group of tuples that agree on the given components.

The groups are `relGroup`'s, but the answer is a set of *accumulators* rather than a set of
relations: `f` runs over each group's tuples starting from `init`, and the result collects one
value of `gamma` per group.

`f` is a function-sorted term, which `Term.lambda` builds. Its two arguments are a tuple of the
relation and the accumulator, in that order, and its result is the new accumulator — so `gamma` is
fixed by `init` and by `f`'s codomain together, and nothing about the fold has to be checked at run
time.

The indices only say what is grouped, so they do not reach the result's sort. With none of them
every tuple is in one group, which is an ordinary fold over the whole relation.
-/
def relAggregate [Ord γ] (indices : Array Nat) (f : Term (Tup α β → γ → γ)) (init : Term γ)
  (rel : Term (Rel α β))
: Env (Term (Set γ)) :=
  T.relAggregate indices f.erase init.erase rel.erase

/-- Equi-join: the product, keeping the pairings whose given component pairs agree.

The result's sort is the product's, since the pairs only filter.
-/
def relTableJoin (indices : Array (Nat × Nat)) (lft : Term (Rel α β)) (rgt : Term (Rel α' β'))
: Env (Term (Rel (α ++ β :: α') β')) :=
  T.relTableJoin indices lft.erase rgt.erase

/-- Projects every tuple onto the given components, in the order given.

Tuple projection lifted to a relation, so it reorders and duplicates as readily as it selects. The
`Cols` spine carries the result's index — `T.relProject` on an `Array Nat` is the sort-erased form,
for positions that are only known at run time.
-/
def relProject (cols : Cols α β α' β') (rel : Term (Rel α β)) : Env (Term (Rel α' β')) :=
  T.relProject cols.toArray rel.erase



/-! ## The set operators, at a relation's index

Same operators, same behaviour; only the index differs, so a relation never has to be read as a set
to be built or constrained.
-/

/-- Whether a tuple is in the relation. -/
def relMember (elm : Term (Tup α β)) (rel : Term (Rel α β)) : Env (Term Bool) :=
  T.setMember elm.erase rel.erase

/-- Whether every tuple of the first relation is in the second. -/
def relSubset (lft rgt : Term (Rel α β)) : Env (Term Bool) :=
  T.setSubset lft.erase rgt.erase

/-- Whether the relation has no tuple. -/
def relIsEmpty (rel : Term (Rel α β)) : Env (Term Bool) := T.setIsEmpty rel.erase

/-- Whether the relation has exactly one tuple. -/
def relIsSingleton (rel : Term (Rel α β)) : Env (Term Bool) := T.setIsSingleton rel.erase

/-- The relation holding exactly one tuple. -/
def relSingleton (elm : Term (Tup α β)) : Env (Term (Rel α β)) := T.setSingleton elm.erase

/-- The relation with one more tuple. -/
def relInsert (elm : Term (Tup α β)) (rel : Term (Rel α β)) : Env (Term (Rel α β)) :=
  T.setInsert elm.erase rel.erase

/-- Union. -/
def relUnion (lft rgt : Term (Rel α β)) : Env (Term (Rel α β)) :=
  T.setUnion lft.erase rgt.erase

/-- N-ary version of `relUnion`, requires at least two elements. -/
def relUnionN (rels : Terms (Rel α β))
  (atLeastTwoElements : 2 ≤ rels.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term (Rel α β)) :=
  T.setUnionN rels atLeastTwoElements

/-- Intersection. -/
def relInter (lft rgt : Term (Rel α β)) : Env (Term (Rel α β)) :=
  T.setInter lft.erase rgt.erase

/-- N-ary version of `relInter`, requires at least two elements. -/
def relInterN (rels : Terms (Rel α β))
  (atLeastTwoElements : 2 ≤ rels.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term (Rel α β)) :=
  T.setInterN rels atLeastTwoElements

/-- Difference. -/
def relMinus (lft rgt : Term (Rel α β)) : Env (Term (Rel α β)) :=
  T.setMinus lft.erase rgt.erase

/-- N-ary version of `relMinus`, requires at least two elements. -/
def relMinusN (rels : Terms (Rel α β))
  (atLeastTwoElements : 2 ≤ rels.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term (Rel α β)) :=
  T.setMinusN rels atLeastTwoElements

/-- Complement, against every tuple of the relation's shape. -/
def relComplement (rel : Term (Rel α β)) : Env (Term (Rel α β)) := T.setComplement rel.erase

/-- How many tuples the relation holds. -/
def relCard (rel : Term (Rel α β)) : Env (Term Int) := T.setCard rel.erase

/-- Some tuple of the relation, unspecified which; undefined on the empty relation. -/
def relChoose (rel : Term (Rel α β)) : Env (Term (Tup α β)) := T.setChoose rel.erase

/-- The tuples satisfying a predicate. -/
def relFilter (p : Term (Tup α β → Bool)) (rel : Term (Rel α β)) : Env (Term (Rel α β)) :=
  T.setFilter p.erase rel.erase

/-- Whether every tuple satisfies a predicate. -/
def relAll (p : Term (Tup α β → Bool)) (rel : Term (Rel α β)) : Env (Term Bool) :=
  T.setAll p.erase rel.erase

/-- Whether some tuple satisfies a predicate. -/
def relSome (p : Term (Tup α β → Bool)) (rel : Term (Rel α β)) : Env (Term Bool) :=
  T.setSome p.erase rel.erase

/-- The empty relation of the given shape. -/
def relEmpty' (α : List Type) (β : Type) [ToTypList α] [ToTyp β] : Env (Term (Rel α β)) := do
  T.setEmpty (← Srt.of (Tup α β))

@[inherit_doc relEmpty']
abbrev relEmpty [ToTypList α] [ToTyp β] : Env (Term (Rel α β)) := relEmpty' α β

/-- The relation holding every tuple of its shape. -/
def relUniverse' (α : List Type) (β : Type) [ToTypList α] [ToTyp β] : Env (Term (Rel α β)) := do
  T.setUniverse (← Srt.of (Tup α β))

@[inherit_doc relUniverse']
abbrev relUniverse [ToTypList α] [ToTyp β] : Env (Term (Rel α β)) := relUniverse' α β
