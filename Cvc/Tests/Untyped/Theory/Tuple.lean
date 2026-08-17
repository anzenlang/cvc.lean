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



/-! # Tuples, sort-erased -/
namespace Cvc.Tests.Untyped.Term.Tuple

open Cvc
open Cvc.Untyped



/-! ## Construction -/

/-- info:
pair   : (tuple 1 true)
sort   : (Tuple Int Bool)
triple : (tuple 1 true (/ 1 2))
sort   : (Tuple Int Bool Real)
nested : (tuple (tuple 1 true) (/ 1 2))
sort   : (Tuple (Tuple Int Bool) Real)
-/
#guard_msgs in #eval Env.runIO do
  let one ← Term.mkInt 1
  let tru ← Term.mkTrue
  let half ← Term.mkReal (1/2 : Rat)

  let pair ← Term.mkTuple #[one, tru]
  println! "pair   : {pair}"
  println! "sort   : {← pair.getSort}"

  let triple ← Term.mkTuple #[one, tru, half]
  println! "triple : {triple}"
  println! "sort   : {← triple.getSort}"

  -- a tuple is an ordinary term, so it nests as a component
  let nested ← Term.mkTuple #[pair, half]
  println! "nested : {nested}"
  println! "sort   : {← nested.getSort}"



/-! ## Projection

`tupleProject` answers a *tuple*, not a component: projecting one index gives a one-component
tuple. It reorders and duplicates as readily as it selects.
-/

/-- info:
[0]     : ((_ tuple.project 0) (tuple 1 true (/ 1 2))) : (Tuple Int)
[2, 0]  : ((_ tuple.project 2 0) (tuple 1 true (/ 1 2))) : (Tuple Real Int)
[1, 1]  : ((_ tuple.project 1 1) (tuple 1 true (/ 1 2))) : (Tuple Bool Bool)
[]      : (tuple.project (tuple 1 true (/ 1 2))) : UnitTuple
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  let show! (indices : Array Nat) (label : String) : Env Unit := do
    let projected ← Term.tupleProject indices triple
    println! "{label}: {projected} : {← projected.getSort}"
  show! #[0] "[0]     "
  show! #[2, 0] "[2, 0]  "
  show! #[1, 1] "[1, 1]  "
  -- projecting nothing is legal: the zero-component tuple
  show! #[] "[]      "



/-! ## Selection

`tupleSelect` is what projection is not: it answers the component itself, at the component's own
sort. There is no kind for it — a tuple sort *is* a datatype, so this is its selector, which is why
cvc5 prints it as `(_ tuple.select i)`.

`fst` and `snd` are the first two indices under names, nothing more — sort-erased there is no index
to get wrong, so they carry no side condition.
-/

/-- info:
select 0 : ((_ tuple.select 0) (tuple 1 true (/ 1 2))) : Int
select 1 : ((_ tuple.select 1) (tuple 1 true (/ 1 2))) : Bool
select 2 : ((_ tuple.select 2) (tuple 1 true (/ 1 2))) : Real
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  for idx in [0 : 3] do
    let component ← Term.tupleSelect idx triple
    println! "select {idx} : {component} : {← component.getSort}"

-- the contrast, on the same term: one index projected is a one-component *tuple*
/-- info:
select  : Bool
project : (Tuple Bool)
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  println! "select  : {← (← Term.tupleSelect 1 triple).getSort}"
  println! "project : {← (← Term.tupleProject #[1] triple).getSort}"

/-- info:
out of range : sort `(Tuple Int Bool Real)` has 3 component(s), so there is none at index 3
not a tuple  : cannot select a component of a term of sort `Int`, which is not a tuple
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"
  println! "out of range : {← caught do pure s!"{← Term.tupleSelect 3 triple}"}"
  println! "not a tuple  : {← caught do pure s!"{← Term.tupleSelect 0 (← Term.mkInt 1)}"}"

/-- info:
fst : ((_ tuple.select 0) (tuple 1 true (/ 1 2))) : Int
snd : ((_ tuple.select 1) (tuple 1 true (/ 1 2))) : Bool
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  println! "fst : {← triple.fst} : {← (← triple.fst).getSort}"
  println! "snd : {← triple.snd} : {← (← triple.snd).getSort}"

/-! Unlike `getTupleValue`, selection works on a *symbolic* tuple: it builds a term rather than
reading a value, so the component comes back out of a model.
-/

/-- info: model fst : 42 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst "x" (← Srt.tuple #[← Srt.int, ← Srt.bool])
  (do Term.equal x (← Term.mkTuple #[← Term.mkInt 42, ← Term.mkFalse])) >>= s.assert
  let fst ← Term.tupleSelect 0 x
  s.checkSat (ifSat := do println! "model fst : {← s.getValueAs Int fst}")


/-! ## Values -/

/-- info:
isTupleValue : true
components   : #[1, true, (/ 1 2)]
not a value  : false
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  println! "isTupleValue : {triple.isTupleValue}"
  println! "components   : {(← triple.getTupleValue).map toString}"

  -- a tuple over a symbol is tuple-sorted but is not a *value*
  let symbolic ← Term.mkTuple #[← Term.mkSymbol (← Srt.int) "x", ← Term.mkTrue]
  println! "not a value  : {symbolic.isTupleValue}"



/-! ## End to end

A tuple equality constrains the components, so the solver answers about them.
-/

/-- info: x = 4 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← s.declareConst "x" (← Srt.int)
  let lft ← Term.mkTuple #[x, ← Term.mkTrue]
  let rgt ← Term.mkTuple #[← Term.mkInt 4, ← Term.mkTrue]
  (do Term.equal lft rgt) >>= s.assert

  s.checkSat (ifSat := do println! "x = {← s.getValueAs Int x}")
