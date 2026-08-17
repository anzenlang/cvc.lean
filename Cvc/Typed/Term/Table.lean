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

public import Cvc.Types.Relation
public import Cvc.Untyped.Term.Table
public import Cvc.Typed.Term.Defs
public import Cvc.Typed.Term.Bag
public import Cvc.Typed.Term.Relation



/-! # Tables, typed

A table is indexed by `Tab α β` — a **bag** of tuples whose columns are `α ++ [β]`. It is the
relation story with duplicates kept, and shares the tuple index and `Components` builder with
`Relation.lean`.

**The bag operators are restated here rather than reached through `Bag`**, so working with a table
never means leaving the table world. `tableUnionMax`, `tableCount` and the rest are the bag
operators at a table's index; `tableToBag` is there for the two that genuinely leave it, `bagMap`
and `bagFold`.

cvc5 marks every table-specific kind experimental.
-/
namespace Cvc.Typed.Term public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## Crossing to and from bags

Both directions are the identity on terms: a table *is* a bag of tuples, and only the index
differs.
-/

/-- Reads a table as the bag of tuples it is. -/
def tableToBag [Ord (Tup α β)] (table : Term (Tab α β)) : Term (Bag (Tup α β)) := table

/-- Reads a bag of tuples as the table it is. -/
def tableOfBag [Ord (Tup α β)] (bag : Term (Bag (Tup α β))) : Term (Tab α β) := bag



/-! ## Table operators -/

/-- Cartesian product: every pairing of rows, with the columns appended. -/
def tableProduct (lft : Term (Tab α β)) (rgt : Term (Tab α' β'))
: Env (Term (Tab (α ++ β :: α') β')) :=
  T.tableProduct lft.erase rgt.erase

/-- Equi-join: the product, keeping the pairings whose given column pairs agree.

The result's sort is the product's, since the pairs only filter.
-/
def tableJoin (columns : Array (Nat × Nat)) (lft : Term (Tab α β)) (rgt : Term (Tab α' β'))
: Env (Term (Tab (α ++ β :: α') β')) :=
  T.tableJoin columns lft.erase rgt.erase

/-- Partitions the table, putting rows that agree on the given columns in the same part.

Answers a bag *of tables*. The columns choose what is compared and so do not reach the result's
sort.
-/
def tableGroup [Ord (Tab α β)] (columns : Array Nat) (table : Term (Tab α β))
: Env (Term (Bag (Tab α β))) :=
  T.tableGroup columns table.erase

/-- Folds each group of rows that agree on the given columns.

The groups are `tableGroup`'s, but the answer is a bag of *accumulators* rather than a bag of
tables: `f` runs over each group's rows starting from `init`, and the result collects one value of
`gamma` per group.

`f` is a function-sorted term, which `Term.lambda` builds. Its two arguments are a row of the table
and the accumulator, in that order, and its result is the new accumulator — so `gamma` is fixed by
`init` and by `f`'s codomain together. This is SQL's `GROUP BY` with an aggregate function.

The columns only say what is grouped, so they do not reach the result's sort. With none of them
every row is in one group, which is an ordinary fold over the whole table.
-/
def tableAggregate [Ord γ] (columns : Array Nat) (f : Term (Tup α β → γ → γ)) (init : Term γ)
  (table : Term (Tab α β))
: Env (Term (Bag γ)) :=
  T.tableAggregate columns f.erase init.erase table.erase

/-- Projects every row onto the given columns, in the order given.

Typed by its `Cols` spine, as `relProject` is; `T.tableProject` on an `Array Nat` is the
sort-erased form, for columns that are only known at run time.
-/
def tableProject (cols : Cols α β α' β') (table : Term (Tab α β)) : Env (Term (Tab α' β')) :=
  T.tableProject cols.toArray table.erase



/-! ## The bag operators, at a table's index -/

/-- Whether a row occurs at least once. -/
def tableMember (row : Term (Tup α β)) (table : Term (Tab α β)) : Env (Term Bool) :=
  T.bagMember row.erase table.erase

/-- Whether every row of the first table occurs at least as often in the second. -/
def tableSubtable (lft rgt : Term (Tab α β)) : Env (Term Bool) :=
  T.bagSubbag lft.erase rgt.erase

/-- The table holding one row, with the given multiplicity. -/
def tableMake (row : Term (Tup α β)) (count : Term Int) : Env (Term (Tab α β)) :=
  T.bagMake row.erase count.erase

/-- How often a row occurs. -/
def tableCount (row : Term (Tup α β)) (table : Term (Tab α β)) : Env (Term Int) :=
  T.bagCount row.erase table.erase

/-- How many rows the table holds, counting duplicates. -/
def tableCard (table : Term (Tab α β)) : Env (Term Int) := T.bagCard table.erase

/-- The table with every multiplicity reduced to one. -/
def tableSetof (table : Term (Tab α β)) : Env (Term (Tab α β)) := T.bagSetof table.erase

/-- Some row of the table, unspecified which; undefined on the empty table. -/
def tableChoose (table : Term (Tab α β)) : Env (Term (Tup α β)) := T.bagChoose table.erase

/-- Union taking the greater multiplicity of each row. -/
def tableUnionMax (lft rgt : Term (Tab α β)) : Env (Term (Tab α β)) :=
  T.bagUnionMax lft.erase rgt.erase

/-- N-ary version of `tableUnionMax`, requires at least two elements. -/
def tableUnionMaxN (tables : Terms (Tab α β))
  (atLeastTwoElements : 2 ≤ tables.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term (Tab α β)) :=
  T.bagUnionMaxN tables atLeastTwoElements

/-- Union adding the multiplicities of each row. -/
def tableUnionDisjoint (lft rgt : Term (Tab α β)) : Env (Term (Tab α β)) :=
  T.bagUnionDisjoint lft.erase rgt.erase

/-- N-ary version of `tableUnionDisjoint`, requires at least two elements. -/
def tableUnionDisjointN (tables : Terms (Tab α β))
  (atLeastTwoElements : 2 ≤ tables.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term (Tab α β)) :=
  T.bagUnionDisjointN tables atLeastTwoElements

/-- Intersection taking the lesser multiplicity of each row. -/
def tableInterMin (lft rgt : Term (Tab α β)) : Env (Term (Tab α β)) :=
  T.bagInterMin lft.erase rgt.erase

/-- N-ary version of `tableInterMin`, requires at least two elements. -/
def tableInterMinN (tables : Terms (Tab α β))
  (atLeastTwoElements : 2 ≤ tables.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term (Tab α β)) :=
  T.bagInterMinN tables atLeastTwoElements

/-- Difference subtracting multiplicities. -/
def tableDifferenceSubtract (lft rgt : Term (Tab α β)) : Env (Term (Tab α β)) :=
  T.bagDifferenceSubtract lft.erase rgt.erase

/-- Difference removing a row entirely wherever it occurs on the right. -/
def tableDifferenceRemove (lft rgt : Term (Tab α β)) : Env (Term (Tab α β)) :=
  T.bagDifferenceRemove lft.erase rgt.erase

/-- The rows satisfying a predicate. -/
def tableFilter (p : Term (Tup α β → Bool)) (table : Term (Tab α β)) : Env (Term (Tab α β)) :=
  T.bagFilter p.erase table.erase

/-- Whether every row satisfies a predicate. -/
def tableAll (p : Term (Tup α β → Bool)) (table : Term (Tab α β)) : Env (Term Bool) :=
  T.bagAll p.erase table.erase

/-- Whether some row satisfies a predicate. -/
def tableSome (p : Term (Tup α β → Bool)) (table : Term (Tab α β)) : Env (Term Bool) :=
  T.bagSome p.erase table.erase

/-- Partitions the rows by an equivalence, answering a bag of tables. -/
def tablePartition [Ord (Tab α β)] (p : Term (Tup α β → Tup α β → Bool)) (table : Term (Tab α β))
: Env (Term (Bag (Tab α β))) :=
  T.bagPartition p.erase table.erase

/-- The empty table of the given shape. -/
def tableEmpty' (α : List Type) (β : Type) [ToTypList α] [ToTyp β] : Env (Term (Tab α β)) := do
  T.bagEmpty (← Srt.of (Tup α β))

@[inherit_doc tableEmpty']
abbrev tableEmpty [ToTypList α] [ToTyp β] : Env (Term (Tab α β)) := tableEmpty' α β
