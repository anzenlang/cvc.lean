/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core
import Cvc.Untyped.Theory
import Cvc.Untyped.Solver

public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory
public meta import Cvc.Untyped.Solver



/-! # Tables, sort-erased

A table is a bag of tuples, so a row can repeat — the only difference from the relations in
`Relation.lean`, whose operators these mirror one for one.
-/
namespace Cvc.Tests.Untyped.Term.Table

open Cvc
open Cvc.Untyped

/-- Two tables, with columns `(Int, Bool)` and `(Bool, String)`. -/
def setup [Ω] : Env (Term × Term) := do
  let s ← Solver.new
  let ab ← Srt.bag (← Srt.tuple #[← Srt.int, ← Srt.bool])
  let bc ← Srt.bag (← Srt.tuple #[← Srt.bool, ← Srt.string])
  return (← s.declareConst "A" ab, ← s.declareConst "B" bc)



/-- info:
product A B    : (Bag (Tuple Int Bool Bool String))
project [1]    : (Bag (Tuple Bool))
project [1, 0] : (Bag (Tuple Bool Int))
join           : (Bag (Tuple Int Bool Bool String))
group [0]      : (Bag (Bag (Tuple Int Bool)))
-/
#guard_msgs in #eval Env.runIO do
  let (a, b) ← setup
  println! "product A B    : {← (← Term.tableProduct a b).getSort}"
  println! "project [1]    : {← (← Term.tableProject #[1] a).getSort}"
  -- columns reorder and duplicate as readily as they select
  println! "project [1, 0] : {← (← Term.tableProject #[1, 0] a).getSort}"
  -- the join's sort is the product's: the column pairs only filter which pairings survive
  println! "join           : {← (← Term.tableJoin #[(1, 0)] a b).getSort}"
  -- grouping answers a bag *of tables*
  println! "group [0]      : {← (← Term.tableGroup #[0] a).getSort}"



/-! ## Solving

The joined table is a sub-bag of the product it filters — which also checks that the two agree on
multiplicities, not just on which rows occur.
-/

/-- info: join ⊑ product : unsat (so every joined row is a product row) -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let ab ← Srt.bag (← Srt.tuple #[← Srt.int, ← Srt.bool])
  let bc ← Srt.bag (← Srt.tuple #[← Srt.bool, ← Srt.string])
  let a ← s.declareConst "A" ab
  let b ← s.declareConst "B" bc
  let joined ← Term.tableJoin #[(1, 0)] a b
  let product ← Term.tableProduct a b
  let sub ← Term.bagSubbag joined product
  (do Term.not sub) >>= s.assert
  println! "join ⊑ product : {
    if ← s.checkIsSat then "SAT" else "unsat (so every joined row is a product row)"}"



/-! ## Aggregating

`tableAggregate` folds each group into a single value, so unlike `tableGroup` its answer is a bag of
*accumulators*: the fold's sort, not the table's. The folding function is an ordinary term of
function sort, which `Term.lambda` builds. This is SQL's `GROUP BY` with an aggregate function.
-/

/-- info:
f       : (lambda ((r (Tuple Int Bool)) (acc Int)) (+ ((_ tuple.select 0) r) acc)) : (-> (Tuple Int Bool) Int Int)
aggr    : ((_ table.aggr 1) (lambda ((r (Tuple Int Bool)) (acc Int)) (+ ((_ tuple.select 0) r) acc)) 0 A) : (Bag Int)
aggrAll : (table.aggr (lambda ((r (Tuple Int Bool)) (acc Int)) (+ ((_ tuple.select 0) r) acc)) 0 A) : (Bag Int)
-/
#guard_msgs in #eval Env.runIO do
  let (a, _b) ← setup
  -- sum the first column, group by the second
  let r ← Term.mkBVar (← Srt.tuple #[← Srt.int, ← Srt.bool]) "r"
  let acc ← Term.mkBVar (← Srt.int) "acc"
  let f ← Term.lambda #[r, acc] (← Term.add (← Term.tupleSelect 0 r) acc)
  println! "f       : {f} : {← f.getSort}"
  let zero ← Term.mkInt 0
  println! "aggr    : {← Term.tableAggregate #[1] f zero a} : {
    ← (← Term.tableAggregate #[1] f zero a).getSort}"
  -- with no column every row is in one group, which is a fold over the whole table
  println! "aggrAll : {← Term.tableAggregate #[] f zero a} : {
    ← (← Term.tableAggregate #[] f zero a).getSort}"

/-! And the fold really runs. Duplicates count, which is what separates this from `relAggregate`:
two copies of `(1, true)` and one of `(10, false)` sum to `2` and `10` grouped by the second column,
and to `12` ungrouped.
-/

/-- info:
aggr    : (bag.union_disjoint (bag 2 1) (bag 10 1))
aggrAll : (bag 12 1)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let int ← Srt.int
  let tup ← Srt.tuple #[int, ← Srt.bool]
  let a ← s.declareConst "A" (← Srt.bag tup)

  let r ← Term.mkBVar tup "r"
  let acc ← Term.mkBVar int "acc"
  let f ← Term.lambda #[r, acc] (← Term.add (← Term.tupleSelect 0 r) acc)
  let zero ← Term.mkInt 0
  let aggr ← Term.tableAggregate #[1] f zero a
  let aggrAll ← Term.tableAggregate #[] f zero a

  let row (i : Int) (b : Bool) (count : Int) : Env Term := do
    Term.bagMake (← Term.mkTuple #[← Term.mkInt i, ← Term.mkBool b]) (← Term.mkInt count)
  let value ← Term.bagUnionDisjointN #[← row 1 true 2, ← row 10 false 1]
  (do Term.equal a value) >>= s.assert

  s.checkSat (ifSat := do
    println! "aggr    : {← s.getValue aggr}"
    println! "aggrAll : {← s.getValue aggrAll}")
