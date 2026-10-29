/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core.Solver
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Core.Solver
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
  s.setLogic Cvc.Logic.qf_lia
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

  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  let three ← Term.mkInt 3

  Term.equal (← Term.add x y) three >>= s.assert
  Term.lt x y >>= s.assert
  println! "assertions : {(← s.getAssertions).size}"

  s.checkSat (ifSat := do
    let vx : Int ← s.getValue x
    let vy : Int ← s.getValue y
    println! "sat        : x = {vx}, y = {vy}")

/-- info: unsat core : 2 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-cores" "true"

  let b ← s.declareConstAs Bool "b"
  s.assert b
  Term.not b >>= s.assert

  let core ← s.checkSat (ifUnsat := do return (← s.getUnsatCore).size)
  println! "unsat core : {core}"

/-- info: unexpected : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let b ← s.declareConstAs Bool "b"
  s.assert b
  let outcome ←
    try
      let _ ← s.checkSat (ifUnsat := do return "unsat")
      pure "no error"
    catch _ => pure "caught"
  println! "unexpected : {outcome}"



/-! ## Interpolants

The sort-erased tests cover the semantics; these pin that the same answers come back indexed at
`Bool`, an interpolant being a formula, and that the absence of one is `none` here too.
-/

/-- Whether `hyps` entail `concl`, by refuting `hyps ∧ ¬concl` on a fresh solver. -/
def entails [Ω] (hyps : Array (Term Bool)) (concl : Term Bool) : Env Bool := do
  let s ← Solver.new
  for h in hyps do s.assert h
  Term.not concl >>= s.assert
  return !(← s.checkIsSat)

/-- info:
interpolant : (and (= a (+ 1 (+ 1 c))) true)
A → I       : true
I → C       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let a ← s.declareConstAs Int "a"
  let b ← s.declareConstAs Int "b"
  let c ← s.declareConstAs Int "c"
  let one ← Term.mkInt 1
  let hyps := #[← Term.equal a (← Term.add b one), ← Term.equal b (← Term.add c one)]
  for h in hyps do s.assert h
  let conj ← Term.gt a c

  let some (i : Term Bool) ← s.getInterpolant conj
    | println! "no interpolant"
  println! "interpolant : {i}"
  println! "A → I       : {← entails hyps i}"
  println! "I → C       : {← entails #[i] conj}"

/-- info: not entailed : none -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let a ← s.declareConstAs Int "a"
  let c ← s.declareConstAs Int "c"
  Term.gt a c >>= s.assert
  println! "not entailed : {← s.getInterpolant (← Term.lt a c)}"

/-- info:
first  : (<= 1 y)
next   : (not (<= y 1))
next   : (or (= y 1) (<= 1 y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  s.setOption "incremental" "true"

  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  let z ← s.declareConstAs Int "z"
  let zero ← Term.mkInt 0
  Term.gt (← Term.add x y) zero >>= s.assert
  Term.lt x zero >>= s.assert
  let conj ← Term.or (← Term.gt (← Term.add y z) zero) (← Term.lt z zero)

  let some first ← s.getInterpolant conj
    | println! "no interpolant"
  println! "first  : {first}"
  for _ in [0:2] do
    let some next ← s.getNextInterpolant
      | println! "exhausted"
    println! "next   : {next}"


/-! ## The signatures state the sorts -/

section signatures
variable [Ω]

/-- info: @Solver.assert : [inst : Ω] → Solver → Term Bool → Env Unit -/
#guard_msgs in #check @Cvc.Typed.Solver.assert

/-- info: @Untyped.Solver.assert : [inst : Ω] → Untyped.Solver → Untyped.Term → Env Unit -/
#guard_msgs in #check @Cvc.Untyped.Solver.assert

/-- info: @Solver.getUnsatCore : [inst : Ω] → (s : Solver) → s.EnvUnsat (Terms Bool) -/
#guard_msgs in #check @Cvc.Typed.Solver.getUnsatCore

/-- info: @Solver.getInterpolant : [inst : Ω] →
  Solver → Term Bool → optParam (Option (Grammar Bool)) none → Env (Option (Term Bool)) -/
#guard_msgs in #check @Cvc.Typed.Solver.getInterpolant

/-- info: @Solver.getNextInterpolant : [inst : Ω] → Solver → Env (Option (Term Bool)) -/
#guard_msgs in #check @Cvc.Typed.Solver.getNextInterpolant

end signatures
