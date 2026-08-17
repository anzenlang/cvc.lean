/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Term.Defs

public import Cvc.Untyped.Term.Defs
-- a relation *is* a set of tuples, so the set operators are what one builds and constrains them
-- with; the tuple constructors are how its elements are made
public import Cvc.Untyped.Term.Set
public import Cvc.Untyped.Term.Tuple



/-! # Relations, sort-erased

A relation is a **set of tuples** — `(Set (Tuple T₁ … Tⱼ))` — and not a sort of its own: there is
no `RELATION_SORT`. So a relation term is built with the set and tuple constructors, and the
operators here are what treat one as a relation.

Tables are the same operators over *bags*, in `Table.lean`. Duplicates being significant is the
only difference between the two families, which are otherwise operator for operator identical.

**cvc5 marks every kind here experimental**, "may be changed or removed in future versions".

`relAggregate` takes its folding function as a *term*, which `Term.lambda` builds.
-/
namespace Cvc.Untyped.Term public section variable [Ω]



/-! ## Operators taking no index -/

/-- Composition: pairs the two relations on `lft`'s last component and `rgt`'s first, dropping it.

Joining `(Set (Tuple Int Bool))` with `(Set (Tuple Bool String))` gives
`(Set (Tuple Int String))`.
-/
def relJoin (lft rgt : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .RELATION_JOIN #[lft, rgt]

/-- Cartesian product: every pairing, with the components appended.

`(Set (Tuple Int Bool))` and `(Set (Tuple Bool String))` give
`(Set (Tuple Int Bool Bool String))`.
-/
def relProduct (lft rgt : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .RELATION_PRODUCT #[lft, rgt]

/-- Reverses each tuple's components, so `(Set (Tuple Int Bool))` becomes `(Set (Tuple Bool Int))`.
-/
def relTranspose (rel : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .RELATION_TRANSPOSE #[rel]

/-- Transitive closure of a homogeneous binary relation, `(Set (Tuple α α))`. -/
def relTclosure (rel : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .RELATION_TCLOSURE #[rel]

/-- The identity relation over a **unary** relation's elements.

Takes `(Set (Tuple α))` and answers `(Set (Tuple α α))`. cvc5 rejects anything else with
`Identity operates on non-unary relations`.
-/
def relIden (rel : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .RELATION_IDEN #[rel]

/-- The elements of a binary relation related to at least `size` others.

Takes `(Set (Tuple α β))` and an integer term, and answers the *unary* relation
`(Set (Tuple α))`.
-/
def relJoinImage (rel : Term) (size : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .RELATION_JOIN_IMAGE #[rel, size]



/-! ## Operators carrying indices

Indices count components from zero, as `tupleProject`'s do, and are what SMT-LIB writes inside
`(_ rel.project 2 0)`.
-/

/-- Projects every tuple onto the given components, in the order given.

Tuple projection lifted to a relation, so it reorders and duplicates as readily as it selects.
-/
def relProject (indices : Array Nat) (rel : Term) : Env Term :=
  runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .RELATION_PROJECT indices) #[rel]

/-- Partitions the relation, putting tuples that agree on the given components in the same part.

Answers a set of relations: `(Set (Tuple Int Bool))` grouped gives
`(Set (Set (Tuple Int Bool)))`. SQL's `GROUP BY`.
-/
def relGroup (indices : Array Nat) (rel : Term) : Env Term :=
  runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .RELATION_GROUP indices) #[rel]

/-- Equi-join: the product of the two relations, keeping the pairings that agree on the given
component pairs.

Each pair is a component of `lft` and one of `rgt` that must be equal. cvc5 takes them interleaved
in one index list, which is what pairing them here rules a mistake out of — the list cannot come
out of odd length. The result's sort is the product's, since the indices only filter.
-/
def relTableJoin (indices : Array (Nat × Nat)) (lft rgt : Term) : Env Term :=
  runUnsafe fun tm => do
    let flat := indices.flatMap fun (l, r) => #[l, r]
    tm.mkTermOfOp (← tm.mkOpOfIndices .RELATION_TABLE_JOIN flat) #[lft, rgt]

/-- Folds each group of tuples that agree on the given components.

`f` is a term of function sort `(Tuple T₁ … Tⱼ) → T → T` — a `Term.lambda` over a tuple bound
variable and an accumulator — and `init` is the accumulator's starting value. The answer is a
`(Set T)`: one entry per group, of the *accumulator's* sort rather than the relation's.

With no index every tuple is in one group, which is an ordinary fold over the whole relation.
-/
def relAggregate (indices : Array Nat) (f init rel : Term) : Env Term :=
  runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .RELATION_AGGREGATE indices) #[f, init, rel]
