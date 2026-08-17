/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Solver

public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Solver



/-! # Tables, typed

A table is indexed by `Tab α β`: a bag of tuples with columns `α ++ [β]` — the relation story with
duplicates kept. It shares the tuple index and its `Components` builder with relations.

Plain `import`, not `import all`, so the index is opaque here exactly as for a user.
-/
namespace Cvc.Tests.Typed.Term.Table

open Cvc
open Cvc
open Cvc.Typed (Term Solver)
open Cvc.Typed.Term

/-- info:
Tab [Int] Bool : (Bag (Tuple Int Bool))
product        : (Bag (Tuple Int Bool Real Real String Bool))
join           : (Bag (Tuple Int Bool Real Real String Bool))
group          : (Bag (Bag (Tuple Int Bool Real)))
-/
#guard_msgs in #eval Env.runIO do
  let sortOf (t : Untyped.Term) : Env String := do return s!"{← t.getSort}"
  let s ← Solver.new
  let abc ← s.declareConst (Tab [Int, Bool] Rat) "A"
  let cde ← s.declareConst (Tab [Rat, String] Bool) "B"
  println! "Tab [Int] Bool : {← (Srt.of (Tab [Int] Bool) : Env Srt)}"
  println! "product        : {← sortOf (← tableProduct abc cde).erase}"
  println! "join           : {← sortOf (← tableJoin #[(2, 0)] abc cde).erase}"
  println! "group          : {← sortOf (← tableGroup #[0] abc).erase}"

-- the bag operators, at a table's index: a table never has to be read as a bag
/-- info:
count      : Int
unionMax   : (Bag (Tuple Int Bool))
unionDisj  : (Bag (Tuple Int Bool))
setof      : (Bag (Tuple Int Bool))
make       : (Bag (Tuple Int Bool))
empty      : (Bag (Tuple Int Bool))
-/
#guard_msgs in #eval Env.runIO do
  let sortOf (t : Untyped.Term) : Env String := do return s!"{← t.getSort}"
  let s ← Solver.new
  let a ← s.declareConst (Tab [Int] Bool) "A"
  let b ← s.declareConst (Tab [Int] Bool) "B"
  let row ← mkTup (.cons (← mkInt 1) (.last (← mkTrue)))
  println! "count      : {← sortOf (← tableCount row a).erase}"
  println! "unionMax   : {← sortOf (← tableUnionMax a b).erase}"
  println! "unionDisj  : {← sortOf (← tableUnionDisjoint a b).erase}"
  println! "setof      : {← sortOf (← tableSetof a).erase}"
  println! "make       : {← sortOf (← tableMake row (← mkInt 3)).erase}"
  let empty : Term (Tab [Int] Bool) ← tableEmpty
  println! "empty      : {← sortOf empty.erase}"

section indices
variable [Ω] (t : Term (Tab [Int, Bool] Rat)) (r : Term (Rel [Int, Bool] Rat))

/-- Grouping nests the row type once. -/
example : Env (Term (Bag (Tab [Int, Bool] Rat))) := tableGroup #[0] t

-- a relation is a *set* of tuples, so it is not a table: the indices keep the families apart
#guard_msgs(drop error) in example := tableGroup #[0] r

end indices

/-! ## Solving

Multiplicity is what distinguishes a table from a relation: three copies of a row make a table of
cardinality three, which a set could not represent.
-/

/-- info: card of 3 copies : 3 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let row ← mkTup (.cons (← mkInt 1) (.last (← mkTrue)))
  let three ← tableMake row (← mkInt 3)
  let card ← tableCard three
  s.checkSat (ifSat := do println! "card of 3 copies : {← s.getValue card}")



/-! ## Aggregating

`tableAggregate` folds each group into one value, so its answer is a `Bag gamma` — the accumulator's
index, not the table's. `gamma` is fixed by `init` and by the folding function's codomain together,
and the function is an ordinary term of arrow index, which `BVars.lambda` builds.
-/

section aggregate
open Cvc.Typed (BVar BVars)

/-- Sums a table's first column, taking the accumulator second, as `tableAggregate` wants. -/
def sumFst [Ω] : Env (Term (Tup [Int] Bool → Int → Int)) := do
  let r ← BVar.mk (α := Tup [Int] Bool) "r"
  let acc ← BVar.mk (α := Int) "acc"
  BVars.lambda (BVars.push acc (BVars.push r [])) (← add (← tupFst r.toTerm) acc.toTerm)

/-- info:
f       : (-> (Tuple Int Bool) Int Int)
aggr    : (Bag Int)
aggrAll : (Bag Int)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let a ← s.declareConst (Tab [Int] Bool) "A"
  let f ← sumFst
  let zero ← mkInt 0
  println! "f       : {← f.erase.getSort}"
  println! "aggr    : {← (← tableAggregate #[1] f zero a).erase.getSort}"
  -- with no column every row is in one group, which is a fold over the whole table
  println! "aggrAll : {← (← tableAggregate #[] f zero a).erase.getSort}"

section indices
variable [Ω]
  (f : Term (Tup [Int] Bool → Int → Int)) (zero : Term Int) (a : Term (Tab [Int] Bool))

/-- The result is a bag of accumulators, not of rows. -/
example : Env (Term (Bag Int)) := tableAggregate #[1] f zero a

-- a relation is a set of tuples, so it is not a table: the indices keep the families apart
#guard_msgs(drop error) in
example [Ω] (r : Term (Rel [Int] Bool)) := tableAggregate #[1] f zero r

end indices

/-! The fold really runs, and duplicates count — which is what separates this from `relAggregate`.
Two copies of `(1, true)` and one of `(10, false)` sum to `2` and `10` grouped by the second column,
and to `12` ungrouped.
-/

/-- info:
aggr    : { 2 ↦ 1, 10 ↦ 1 }
aggrAll : { 12 ↦ 1 }
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let a ← s.declareConst (Tab [Int] Bool) "A"
  let f ← sumFst
  let zero ← mkInt 0
  let aggr ← tableAggregate #[1] f zero a
  let aggrAll ← tableAggregate #[] f zero a

  let row (i : Int) (b : Bool) (count : Int) : Env (Term (Tab [Int] Bool)) := do
    tableMake (← mkTup (.cons (← mkInt i) (.last (← mkBool b)))) (← mkInt count)
  let value ← tableUnionDisjoint (← row 1 true 2) (← row 10 false 1)
  (do equal a value) >>= s.assert

  s.checkSat (ifSat := do
    println! "aggr    : {← s.getValue aggr}"
    println! "aggrAll : {← s.getValue aggrAll}")

end aggregate



/-! ## The n-ary spellings

`tableUnionMaxN`, `tableUnionDisjointN` and `tableInterMinN` are the bag operators' n-ary variants
at a table's index, carrying the same `2 ≤ size` autoparam.
-/

/-- info:
unionMaxN      : (Bag (Tuple Int Bool))
unionDisjointN : (Bag (Tuple Int Bool))
interMinN      : (Bag (Tuple Int Bool))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let a ← s.declareConst (Tab [Int] Bool) "A"
  let b ← s.declareConst (Tab [Int] Bool) "B"
  let c ← s.declareConst (Tab [Int] Bool) "C"
  println! "unionMaxN      : {← (← tableUnionMaxN #[a, b, c]).erase.getSort}"
  println! "unionDisjointN : {← (← tableUnionDisjointN #[a, b, c]).erase.getSort}"
  println! "interMinN      : {← (← tableInterMinN #[a, b, c]).erase.getSort}"

section indices
variable [Ω] (a b : Term (Tab [Int] Bool)) (r : Term (Rel [Int] Bool))

/-- The result is a table at the shared index. -/
example : Env (Term (Tab [Int] Bool)) := tableUnionMaxN #[a, b]

-- fewer than two elements: the autoparam has nothing to prove it from
#guard_msgs(drop error) in example := tableUnionMaxN #[a]

-- a relation is a set of tuples, so it does not belong in an array of tables
#guard_msgs(drop error) in example := tableUnionMaxN #[a, r]

end indices

/-! Multiplicity is what separates the two unions: three copies of one row union to three disjointly
and to one at the maximum.
-/

/-- info:
card of unionDisjointN : 3
card of unionMaxN      : 1
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let row ← mkTup (.cons (← mkInt 1) (.last (← mkTrue)))
  let one ← tableMake row (← mkInt 1)
  let disjoint ← tableCard (← tableUnionDisjointN #[one, one, one])
  let max ← tableCard (← tableUnionMaxN #[one, one, one])
  s.checkSat (ifSat := do
    println! "card of unionDisjointN : {← s.getValue disjoint}"
    println! "card of unionMaxN      : {← s.getValue max}")



/-! ## Projection

`tableProject` is typed by the same `Cols` spine `relProject` uses — see the relation tests for the
positions themselves, which are shared. What is worth pinning here is that projection is a *bag*
operation: it maps each row and keeps every one, so rows that differ only in a dropped column
become the same row rather than merging.
-/

/-- A four-column table, so that a middle column has somewhere to be. -/
abbrev B4 := Tab [Int, Bool, String] Rat

/-- info:
table          : (Bag (Tuple Int Bool String Real))
project [2, 0] : (Bag (Tuple String Int))
project [3, 3] : (Bag (Tuple Real Real))
project [1]    : (Bag (Tuple Bool))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let b ← s.declareConst B4 "B"
  let sortOf (t : Untyped.Term) : Env String := do return s!"{← t.getSort}"
  println! "table          : {← sortOf b.erase}"
  -- reordering, duplication, and a one-column result that is still a tuple
  println! "project [2, 0] : {← sortOf (← tableProject cols% [2, 0] b).erase}"
  println! "project [3, 3] : {← sortOf (← tableProject cols% [3, 3] b).erase}"
  println! "project [1]    : {← sortOf (← tableProject cols% [1] b).erase}"

section indices
variable [Ω] (b : Term B4) (r : Term (Rel [Int, Bool, String] Rat))

/-- The result index is the columns selected, in the order selected. -/
example : Env (Term (Tab [String] Int)) := tableProject cols% [2, 0] b
/-- One column still gives a table of one-column rows. -/
example : Env (Term (Tab [] Bool)) := tableProject cols% [1] b

-- a relation is a set of tuples, so the table projection does not apply to it
#guard_msgs(drop error) in example := tableProject cols% [2, 0] r

end indices

/-! Two rows that agree on the projected columns and differ elsewhere give **two** rows, not one —
the multiplicity is what a table keeps and a relation does not. `tableSetof` is how to ask for the
relation-like answer.
-/

/-- info:
rows after projecting onto [2, 1] : 2
distinct rows                     : 1
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let row (i : Int) : Env (Term (Tup [Int, Bool, String] Rat)) := do
    mkTup <| .cons (← mkInt i) <| .cons (← mkTrue) <| .cons (← mkString "a" false)
      <| .last (← mkReal (1/2 : Rat))
  -- the two rows differ only in column 0, which the projection drops
  let b ← tableUnionDisjoint (← tableMake (← row 1) (← mkInt 1))
    (← tableMake (← row 2) (← mkInt 1))
  let projected ← tableProject cols% [2, 1] b
  let card ← tableCard projected
  let distinct ← tableCard (← tableSetof projected)
  s.checkSat (ifSat := do
    println! "rows after projecting onto [2, 1] : {← s.getValue card}"
    println! "distinct rows                     : {← s.getValue distinct}")
