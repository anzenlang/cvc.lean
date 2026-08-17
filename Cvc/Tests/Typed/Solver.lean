/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Solver
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Solver
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # The solver, typed

Only the functions shared by both layers are covered here: the ones mentioning a term belong to
whichever layer states their sorts.
-/
namespace Cvc.Tests.Typed.Solver

open Cvc
open Cvc.Typed

/-! ## Options and information -/

/-- info:
option set  : true
option unset: false
info set    : ok
names       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Typed.Solver.new

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
  let s ← Cvc.Typed.Solver.new
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
  let s ← Cvc.Typed.Solver.new

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
  let s ← Cvc.Typed.Solver.new
  let version ← s.getVersion
  println! "version : {!version.isEmpty}"

/-! ## Asserting and checking

From here the signatures mention terms, so the two layers differ: this one takes `Bool`-indexed
formulas, and reads a model value back as the Lean value its index describes.
-/

/-- info:
assertions : 2
sat        : x = 1, y = 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← s.declareConst Int "x"
  let y ← s.declareConst Int "y"
  let three ← Term.mkInt 3

  (do Term.equal (← Term.add x y) three) >>= s.assert
  (do Term.lt x y) >>= s.assert
  println! "assertions : {(← s.getAssertions).size}"

  s.checkSat (ifSat := do
    let vx : Int ← s.getValue x
    let vy : Int ← s.getValue y
    println! "sat        : x = {vx}, y = {vy}")

/-- info: unsat core : 2 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-cores" "true"

  let b ← s.declareConst Bool "b"
  s.assert b
  (do Term.not b) >>= s.assert

  let core ← s.checkSat (ifUnsat := do return (← s.getUnsatCore).size)
  println! "unsat core : {core}"

/-- info: unexpected : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let b ← s.declareConst Bool "b"
  s.assert b
  let outcome ←
    try
      let _ ← s.checkSat (ifUnsat := do return "unsat")
      pure "no error"
    catch _ => pure "caught"
  println! "unexpected : {outcome}"



/-! ## The signatures state the sorts -/

section signatures
variable [Ω]

/-- info: @Solver.assert : [inst : Ω] → Solver → Term Bool → Env Unit -/
#guard_msgs in #check @Cvc.Typed.Solver.assert

/-- info: @Untyped.Solver.assert : [inst : Ω] → Untyped.Solver → Untyped.Term → Env Unit -/
#guard_msgs in #check @Cvc.Untyped.Solver.assert

/-- info: @Solver.getUnsatCore : [inst : Ω] → Solver → EnvUnsat (Terms Bool) -/
#guard_msgs in #check @Cvc.Typed.Solver.getUnsatCore

end signatures
