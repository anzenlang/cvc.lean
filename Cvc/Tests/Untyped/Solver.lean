/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Solver
import Cvc.Untyped.Theory.Arith

meta import Cvc.Untyped.Solver
meta import Cvc.Untyped.Theory.Arith



/-! # The solver, sort-erased

Only the functions shared by both layers are covered here: the ones mentioning a term belong to
whichever layer states their sorts.
-/
namespace Cvc.Tests.Untyped.Solver

open Cvc
open Cvc.Untyped

/-! ## Options and information -/

/-- info:
option set  : true
option unset: false
info set    : ok
names       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new

  s.setOption "produce-models" "true"
  println! "option set  : {← s.getOption "produce-models"}"
  s.setOption "produce-models" "false"
  println! "option unset: {← s.getOption "produce-models"}"

  s.setInfo "status" "sat"
  println! "info set    : ok"

  let names ← s.getOptionNames
  println! "names       : {!names.isEmpty}"



/-! ## The logic -/

/-- info:
before : false
after  : true
name   : QF_LIA
parsed : QF_LIA
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  println! "before : {← s.isLogicSet}"
  s.setLogic Cvc.Logic.qf_lia.toLogic
  println! "after  : {← s.isLogicSet}"
  println! "name   : {← s.getLogicString}"
  println! "parsed : {(← s.getLogic).toSmtLib}"



/-! ## Assertion scopes and sorts -/

/-- info:
pushed  : ok
popped  : ok
reset   : ok
sort    : U
sort 2  : Pair
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new

  s.push
  println! "pushed  : ok"
  s.pop
  println! "popped  : ok"
  s.reset
  println! "reset   : ok"

  println! "sort    : {← s.declareSrt "U" 0}"
  println! "sort 2  : {← s.declareSrt "Pair" 2}"



/-! ## Version -/

/-- info: version : true -/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  let version ← s.getVersion
  println! "version : {!version.isEmpty}"

/-! ## Asserting and checking

From here the signatures mention terms, so the two layers differ: this one takes and returns
sort-erased terms.
-/

/-- info:
assertions : 2
sat        : x = 1, y = 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  let three ← Term.mkInt 3

  (do Term.equal (← Term.add x y) three) >>= s.assert
  (do Term.lt x y) >>= s.assert
  println! "assertions : {(← s.getAssertions).size}"

  s.checkSat (ifSat := do
    println! "sat        : x = {← s.getValue x}, y = {← s.getValue y}")

/-- info: unsat core : 2 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-cores" "true"

  let bool ← Srt.bool
  let b ← s.declareConst "b" bool
  s.assert b
  (do Term.not b) >>= s.assert

  let core ← s.checkSat (ifUnsat := do return (← s.getUnsatCore).size)
  println! "unsat core : {core}"

/-- info: unexpected : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let bool ← Srt.bool
  let b ← s.declareConst "b" bool
  s.assert b
  -- only an unsat branch is given, and the solver answers sat
  let outcome ←
    try
      let _ ← s.checkSat (ifUnsat := do return "unsat")
      pure "no error"
    catch _ => pure "caught"
  println! "unexpected : {outcome}"
