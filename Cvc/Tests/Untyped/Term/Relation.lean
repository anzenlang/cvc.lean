/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Term
import Cvc.Untyped.Solver

public meta import Cvc.Untyped.Term
public meta import Cvc.Untyped.Solver



/-! # Relations, sort-erased

A relation is a set of tuples, not a sort of its own, so what these tests pin is the *sort* each
operator answers at — which is the whole content of the family.
-/
namespace Cvc.Tests.Untyped.Term.Relation

open Cvc
open Cvc.Untyped

/-- Four relations: `(Int, Bool)`, `(Bool, String)`, `(Int, Int)` and the unary `(Int)`. -/
def setup [Ω] : Env (Term × Term × Term × Term) := do
  let s ← Solver.new
  let int ← Srt.int
  let ab ← Srt.set (← Srt.tuple #[int, ← Srt.bool])
  let bc ← Srt.set (← Srt.tuple #[← Srt.bool, ← Srt.string])
  let aa ← Srt.set (← Srt.tuple #[int, int])
  let un ← Srt.set (← Srt.tuple #[int])
  return (← s.declareConst "A" ab, ← s.declareConst "B" bc,
          ← s.declareConst "R" aa, ← s.declareConst "U" un)



/-! ## Operators taking no index -/

/-- info:
join A B     : (Set (Tuple Int String))
product A B  : (Set (Tuple Int Bool Bool String))
transpose A  : (Set (Tuple Bool Int))
tclosure R   : (Set (Tuple Int Int))
iden U       : (Set (Tuple Int Int))
joinImage R  : (Set (Tuple Int))
-/
#guard_msgs in #eval Env.runIO do
  let (a, b, r, u) ← setup
  -- join drops the component the two relations meet on
  println! "join A B     : {← (← Term.relJoin a b).getSort}"
  -- product appends every component of both
  println! "product A B  : {← (← Term.relProduct a b).getSort}"
  println! "transpose A  : {← (← Term.relTranspose a).getSort}"
  println! "tclosure R   : {← (← Term.relTclosure r).getSort}"
  -- identity takes a *unary* relation and pairs each element with itself
  println! "iden U       : {← (← Term.relIden u).getSort}"
  -- join image answers a unary relation
  println! "joinImage R  : {← (← Term.relJoinImage r (← Term.mkInt 2)).getSort}"

/-! `relIden` is the one with a shape requirement cvc5 states outright. -/

/-- info: iden on binary : [internal] Identity operates on non-unary relations -/
#guard_msgs in #eval Env.runIO do
  let (a, _b, _r, _u) ← setup
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"
  println! "iden on binary : {← caught do pure s!"{← Term.relIden a}"}"



/-! ## Operators carrying indices

Indices count components from zero. Projection reorders and duplicates as readily as it selects,
exactly as `tupleProject` does; grouping answers a set *of relations*.
-/

/-- info:
project [1]    : (Set (Tuple Bool))
project [1, 0] : (Set (Tuple Bool Int))
group [0]      : (Set (Set (Tuple Int Bool)))
tableJoin      : (Set (Tuple Int Bool Bool String))
-/
#guard_msgs in #eval Env.runIO do
  let (a, b, _r, _u) ← setup
  println! "project [1]    : {← (← Term.relProject #[1] a).getSort}"
  println! "project [1, 0] : {← (← Term.relProject #[1, 0] a).getSort}"
  println! "group [0]      : {← (← Term.relGroup #[0] a).getSort}"
  -- the join's sort is the product's: the column pairs only filter which pairings survive
  println! "tableJoin      : {← (← Term.relTableJoin #[(1, 0)] a b).getSort}"



/-! ## Solving

An equi-join on the one shared column, against the product it filters.
-/

/-- info: join ⊆ product : unsat (so every joined pair is a product pair) -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let int ← Srt.int
  let ab ← Srt.set (← Srt.tuple #[int, ← Srt.bool])
  let bc ← Srt.set (← Srt.tuple #[← Srt.bool, ← Srt.string])
  let a ← s.declareConst "A" ab
  let b ← s.declareConst "B" bc
  let joined ← Term.relTableJoin #[(1, 0)] a b
  let product ← Term.relProduct a b
  -- a joined row that is not a product row would be a counterexample
  let sub ← Term.setSubset joined product
  (do Term.not sub) >>= s.assert
  println! "join ⊆ product : {
    if ← s.checkIsSat then "SAT" else "unsat (so every joined pair is a product pair)"}"



/-! ## Aggregating

`relAggregate` folds each group into a single value, so unlike `relGroup` its answer is a set of
*accumulators*: the fold's sort, not the relation's. The folding function is an ordinary term of
function sort, which `Term.lambda` builds.
-/

/-- info:
f       : (lambda ((t (Tuple Int Bool)) (acc Int)) (+ ((_ tuple.select 0) t) acc)) : (-> (Tuple Int Bool) Int Int)
aggr    : ((_ rel.aggr 1) (lambda ((t (Tuple Int Bool)) (acc Int)) (+ ((_ tuple.select 0) t) acc)) 0 A) : (Set Int)
aggrAll : (rel.aggr (lambda ((t (Tuple Int Bool)) (acc Int)) (+ ((_ tuple.select 0) t) acc)) 0 A) : (Set Int)
-/
#guard_msgs in #eval Env.runIO do
  let (a, _b, _r, _u) ← setup
  -- sum the first component, group by the second
  let t ← Term.mkBVar (← Srt.tuple #[← Srt.int, ← Srt.bool]) "t"
  let acc ← Term.mkBVar (← Srt.int) "acc"
  let f ← Term.lambda #[t, acc] (← Term.add (← Term.tupleSelect 0 t) acc)
  println! "f       : {f} : {← f.getSort}"
  let zero ← Term.mkInt 0
  println! "aggr    : {← Term.relAggregate #[1] f zero a} : {
    ← (← Term.relAggregate #[1] f zero a).getSort}"
  -- with no index every tuple is in one group, which is a fold over the whole relation
  println! "aggrAll : {← Term.relAggregate #[] f zero a} : {
    ← (← Term.relAggregate #[] f zero a).getSort}"

/-! And the fold really runs: `{(1, true), (2, true), (10, false)}` sums to `3` and `10` grouped by
its second component, and to `13` ungrouped.
-/

/-- info:
aggr    : (set.union (set.singleton 3) (set.singleton 10))
aggrAll : (set.singleton 13)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let int ← Srt.int
  let tup ← Srt.tuple #[int, ← Srt.bool]
  let a ← s.declareConst "A" (← Srt.set tup)

  let t ← Term.mkBVar tup "t"
  let acc ← Term.mkBVar int "acc"
  let f ← Term.lambda #[t, acc] (← Term.add (← Term.tupleSelect 0 t) acc)
  let zero ← Term.mkInt 0
  let aggr ← Term.relAggregate #[1] f zero a
  let aggrAll ← Term.relAggregate #[] f zero a

  let tuple (i : Int) (b : Bool) : Env Term := do
    Term.setSingleton (← Term.mkTuple #[← Term.mkInt i, ← Term.mkBool b])
  let value ← Term.setUnionN #[← tuple 1 true, ← tuple 2 true, ← tuple 10 false]
  (do Term.equal a value) >>= s.assert

  s.checkSat (ifSat := do
    println! "aggr    : {← s.getValue aggr}"
    println! "aggrAll : {← s.getValue aggrAll}")
