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

  Term.equal (← Term.add x y) three >>= s.assert
  Term.lt x y >>= s.assert
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
  Term.not b >>= s.assert

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



/-! ## Interpolants

An interpolant of assertions `A` and a conjecture `C` is a formula `I` over the symbols both
mention, such that `A → I` and `I → C`. The first test checks both implications with a second
solver rather than trusting the answer's shape, so it pins what an interpolant *is* and not only
how cvc5 prints this one.

cvc5 answers the null term when there is no interpolant, and when an enumeration runs out; that is
`none` here.
-/

/-- Whether `hyps` entail `concl`, by refuting `hyps ∧ ¬concl` on a fresh solver. -/
def entails [Ω] (hyps : Array Term) (concl : Term) : Env Bool := do
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

  let int ← Srt.int
  let a ← s.declareConst "a" int
  let b ← s.declareConst "b" int
  let c ← s.declareConst "c" int
  let one ← Term.mkInt 1
  -- `b` is not shared with the conjecture, so the interpolant has to eliminate it
  let hyps := #[← Term.equal a (← Term.add b one), ← Term.equal b (← Term.add c one)]
  for h in hyps do s.assert h
  let conj ← Term.gt a c

  let some i ← s.getInterpolant conj
    | println! "no interpolant"
  println! "interpolant : {i}"
  println! "A → I       : {← entails hyps i}"
  println! "I → C       : {← entails #[i] conj}"

/-- info: not entailed : none -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let int ← Srt.int
  let a ← s.declareConst "a" int
  let c ← s.declareConst "c" int
  Term.gt a c >>= s.assert
  -- the assertions do not entail the conjecture, so nothing can sit between them
  println! "not entailed : {← s.getInterpolant (← Term.lt a c)}"

/-- info:
first  : (<= 1 y)
next   : (not (<= y 1))
next   : (or (= y 1) (<= 1 y))
all distinct : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  s.setOption "incremental" "true"

  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  let z ← s.declareConst "z" int
  let zero ← Term.mkInt 0
  Term.gt (← Term.add x y) zero >>= s.assert
  Term.lt x zero >>= s.assert
  let conj ← Term.or (← Term.gt (← Term.add y z) zero) (← Term.lt z zero)

  let some first ← s.getInterpolant conj
    | println! "no interpolant"
  println! "first  : {first}"
  let mut seen := #[first]
  for _ in [0:2] do
    let some next ← s.getNextInterpolant
      | println! "exhausted"
    println! "next   : {next}"
    seen := seen.push next
  println! "all distinct : {seen.all fun t => (seen.filter (· == t)).size == 1}"

/-- info: next, not incremental : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  s.setOption "incremental" "false"

  let int ← Srt.int
  let a ← s.declareConst "a" int
  let c ← s.declareConst "c" int
  Term.gt a c >>= s.assert
  let _ ← s.getInterpolant (← Term.ge a c)
  let outcome ←
    try
      let _ ← s.getNextInterpolant
      pure "no error"
    catch _ => pure "caught"
  println! "next, not incremental : {outcome}"

/-- info: without the option : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let int ← Srt.int
  let a ← s.declareConst "a" int
  let outcome ←
    try
      let _ ← s.getInterpolant (← Term.equal a a)
      pure "no error"
    catch _ => pure "caught"
  println! "without the option : {outcome}"
