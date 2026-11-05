/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

-- a table *is* a bag of tuples, so the bag operators are what one builds and constrains them with;
-- the tuple constructors are how its rows are made
public import Cvc.Untyped.Theory.Bag
public import Cvc.Untyped.Theory.Tuple



/-! # Tables, sort-erased

A table is a **bag of tuples** — `(Bag (Tuple T₁ … Tⱼ))` — and not a sort of its own: there is no
`TABLE_SORT`. These are relational-database tables, so a row can repeat, which is the whole
difference from the relations in `Relation.lean`. The two families are otherwise operator for
operator the same.

**cvc5 marks every kind here experimental**, "may be changed or removed in future versions".

`tableAggregate` takes its folding function as a *term*, which `Term.lambda` builds.
-/
namespace Cvc.Untyped.Term public section variable [Ω]



/-- Cartesian product: every pairing of rows, with the columns appended. -/
def tableProduct (lft rgt : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .TABLE_PRODUCT #[lft, rgt]

/-- Projects every row onto the given columns, in the order given.

Columns count from zero, and need be neither increasing nor distinct, so this reorders and
duplicates as readily as it selects.
-/
def tableProject (columns : Array Nat) (table : Term) : Env Term :=
  runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .TABLE_PROJECT columns) #[table]

/-- Equi-join: the product of the two tables, keeping the pairings whose given columns agree.

Each pair is a column of `lft` and one of `rgt` that must be equal. cvc5 takes them interleaved in
one index list, which is what pairing them here rules a mistake out of — the list cannot come out
of odd length. The result's sort is the product's, since the columns only filter.
-/
def tableJoin (columns : Array (Nat × Nat)) (lft rgt : Term) : Env Term :=
  runUnsafe fun tm => do
    let flat := columns.flatMap fun (l, r) => #[l, r]
    tm.mkTermOfOp (← tm.mkOpOfIndices .TABLE_JOIN flat) #[lft, rgt]

/-- Partitions the table, putting rows that agree on the given columns in the same part.

Answers a bag of tables: `(Bag (Tuple Int Bool))` grouped gives `(Bag (Bag (Tuple Int Bool)))`.
SQL's `GROUP BY`.
-/
def tableGroup (columns : Array Nat) (table : Term) : Env Term :=
  runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .TABLE_GROUP columns) #[table]

/-- Folds each group of rows that agree on the given columns.

`f` is a term of function sort `(Tuple T₁ … Tⱼ) → T → T` — a `Term.lambda` over a row bound
variable and an accumulator — and `init` is the accumulator's starting value. The answer is a
`(Bag T)`: one entry per group, of the *accumulator's* sort rather than the table's.

With no column every row is in one group, which is an ordinary fold over the whole table.
-/
def tableAggregate (columns : Array Nat) (f init table : Term) : Env Term :=
  runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .TABLE_AGGREGATE columns) #[f, init, table]
