/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Synth
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Synth
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory



/-! # Syntax-guided synthesis, sort-erased -/
namespace Cvc.Tests.Untyped.Synth

open Cvc
open Cvc.Untyped



/-! ## Synthesizing under a grammar

The specification says `max` and the grammar says which shapes are allowed, so what comes back is
one of those shapes.
-/

/-- info:
constraints : 3
solution    : (lambda ((x Int) (y Int)) (ite (<= y x) x y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int

  let x ← BVar.mk int "x"
  let y ← BVar.mk int "y"

  let start ← NT.mk int "start"
  let cnd ← NT.mk (← Srt.bool) "cnd"
  let g ← s.mkGrammar #[x, y] start #[cnd]
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start y.toTerm
  let g ← g.addRule start (← Term.ite cnd start.toTerm start.toTerm)
  let g ← g.addRule cnd (← Term.le start.toTerm start.toTerm)

  let mx ← s.synthFun "max" #[x, y] int g

  -- the variables the specification quantifies over
  let a ← s.declareSygusVar "a" int
  let b ← s.declareSygusVar "b" int
  let mab ← Term.apply2 mx a b
  s.addSygusConstraint (← Term.ge mab a)
  s.addSygusConstraint (← Term.ge mab b)
  s.addSygusConstraint (← Term.or (← Term.equal mab a) (← Term.equal mab b))
  println! "constraints : {(← s.getSygusConstraints).size}"

  s.checkSynth (ifSolved := do
    println! "solution    : {← s.getSynthSolution mx}")



/-! ## Without a grammar

`synthFun` takes an optional grammar, so leaving it out allows any term of the right sort.
-/

/-- info:
solution : (lambda ((x Int)) (+ x 1))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int

  let x ← BVar.mk int "x"
  let f ← s.synthFun "f" #[x] int

  let a ← s.declareSygusVar "a" int
  s.addSygusConstraint (← Term.equal (← Term.apply f a) (← Term.add a (← Term.mkInt 1)))

  s.checkSynth (ifSolved := do
    println! "solution : {← s.getSynthSolution f}")



/-! ## A conjecture with no solution

`isSolved?` is the three-way answer: `some true` solved, `some false` unsolvable, `none` gave up.
Here the grammar allows only the two projections, and neither is a `max`.
-/

/-- info:
branch    : unsolvable
hasSolution   : false
isSolved?     : (some false)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int

  let x ← BVar.mk int "x"
  let y ← BVar.mk int "y"
  let start ← NT.mk int "start"
  let g ← s.mkGrammar #[x, y] start
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start y.toTerm

  let mx ← s.synthFun "max" #[x, y] int g
  let a ← s.declareSygusVar "a" int
  let b ← s.declareSygusVar "b" int
  let mab ← Term.apply2 mx a b
  s.addSygusConstraint (← Term.ge mab a)
  s.addSygusConstraint (← Term.ge mab b)

  -- the branch that runs is the one matching the answer; the others reject it
  s.checkSynth (ifUnsolvable := do println! "branch    : unsolvable")

  let res ← s.checkSynthResult
  println! "hasSolution   : {res.hasSolution}"
  println! "isSolved?     : {← res.isSolved?}"



/-! ## Assumptions

`addSygusAssume` weakens the conjecture: the constraints need only hold where the assumptions do.
-/

/-- info:
assumptions : 1
solved      : yes
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int

  let x ← BVar.mk int "x"
  let f ← s.synthFun "f" #[x] int

  let a ← s.declareSygusVar "a" int
  -- only positive inputs are constrained, so a solution exists that would not otherwise
  s.addSygusAssume (← Term.gt a (← Term.mkInt 0))
  s.addSygusConstraint (← Term.gt (← Term.apply f a) (← Term.mkInt 0))
  println! "assumptions : {(← s.getSygusAssumptions).size}"

  s.checkSynth (ifSolved := do println! "solved      : yes")



/-! ## An unexpected answer is rejected

A branch the caller did not supply throws, so a synthesis result cannot be quietly ignored.
-/

/-- info: unexpected : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int

  let x ← BVar.mk int "x"
  let f ← s.synthFun "f" #[x] int
  let a ← s.declareSygusVar "a" int
  s.addSygusConstraint (← Term.equal (← Term.apply f a) a)

  -- this one *is* solvable, so the unsolvable-only branch rejects it
  let outcome ←
    try
      s.checkSynth (ifUnsolvable := do return "no error")
    catch _ => pure "caught"
  println! "unexpected : {outcome}"



/-! ## A solution can only be read where one was found

`getSynthSolution` lives in `EnvSolved`, which `checkSynth` is the only way into. Asking for one
outside a solved branch does not typecheck.
-/

/-- error: Type mismatch
  s.getSynthSolution f
has type
  s.EnvSolved Term
but is expected to have type
  Env Term -/
#guard_msgs in
example [Ω] (s : Solver) (f : Term) : Env Term := s.getSynthSolution f



/-! ## Enumerating terms

`findSynth` enumerates terms of interest rather than solving a conjecture, and `findSynthNext`
continues the enumeration. cvc5 answers the null term when one runs out, which is `none` here, and
the `!` forms fail instead. A grammar with two terms is exhausted on the third call.
-/

/-- info:
first : (some true)
next  : (some false)
next  : none
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let start ← NT.mk (← Srt.bool) "start"
  let g ← s.mkGrammar #[] start
  let g ← g.addRules start #[← Term.mkBool true, ← Term.mkBool false]
  println! "first : {← s.findSynth .enum g}"
  println! "next  : {← s.findSynthNext}"
  println! "next  : {← s.findSynthNext}"

/-- info:
first! : true
next!  : false
next!  : cvc5 found no further term of interest
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let start ← NT.mk (← Srt.bool) "start"
  let g ← s.mkGrammar #[] start
  let g ← g.addRules start #[← Term.mkBool true, ← Term.mkBool false]
  println! "first! : {← s.findSynth! .enum g}"
  println! "next!  : {← s.findSynthNext!}"
  try println! "next!  : {← s.findSynthNext!}"
  catch e => println! "next!  : {e}"

/-! Without a grammar, `findSynth` enumerates over the grammar of the last `synthFun` given one,
and cvc5 refuses when there is none. -/

/-- info:
after synthFun : (some true)
without one    : [internal] No grammar available in call to find-synth. Either provide one or ensure synth-fun has been called.
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let start ← NT.mk (← Srt.bool) "start"
  let g ← s.mkGrammar #[] start
  let g ← g.addRules start #[← Term.mkBool true, ← Term.mkBool false]
  let _ ← s.synthFun "f" #[] (← Srt.bool) g
  println! "after synthFun : {← s.findSynth .enum}"
  let s ← Solver.new
  s.setOption "sygus" "true"
  let _ ← s.synthFun "f" #[] (← Srt.bool)
  try println! "without one    : {← s.findSynth .enum}"
  catch e => println! "without one    : {e}"



/-! ## Further solutions

`checkSynthNext` asks for another solution where one was found, and runs the branch matching the
answer, so it nests: each solution here differs from the ones before, and each satisfies `a < f a`.
`checkSynthNextResult` is the raw form.
-/

/-- info:
first : (lambda ((x Int)) (+ 1 x))
next  : (lambda ((x Int)) (+ (+ 1 x) 1))
next  : (lambda ((x Int)) (+ (+ (+ 1 1) 1) x))
raw   : (SOLUTION), hasSolution: true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let x ← BVar.mk int "x"
  let f ← s.synthFun "f" #[x] int
  let a ← s.declareSygusVar "a" int
  s.addSygusConstraint (← smt! a < f a)
  s.checkSynth (ifSolved := do
    println! "first : {← s.getSynthSolution f}"
    s.checkSynthNext (ifSolved := do
      println! "next  : {← s.getSynthSolution f}"
      s.checkSynthNext (ifSolved := do
        println! "next  : {← s.getSynthSolution f}")))
  let r ← s.checkSynthNextResult
  println! "raw   : {r}, hasSolution: {r.hasSolution}"



/-! ## Several functions at once

`getSynthSolutions` answers one solution per function, in the order asked, and the solutions agree
with each other: `g` is stated in terms of `f`.
-/

/-- info: solutions : #[(lambda ((x Int)) (+ (+ 2 x) x)), (lambda ((x Int)) (+ 1 x))] -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let x ← BVar.mk int "x"
  let f ← s.synthFun "f" #[x] int
  let g ← s.synthFun "g" #[x] int
  let a ← s.declareSygusVar "a" int
  s.addSygusConstraint (← smt! f a = a + 1)
  s.addSygusConstraint (← smt! g a = f a + f a)
  s.checkSynth (ifSolved := do println! "solutions : {← s.getSynthSolutions #[g, f]}")



/-! ## Invariants

`addSygusInvConstraint` asks for an inductive invariant of a transition system given as defined
functions: a counter starting at `0` and incremented while below `10` never exceeds `10`, and with
`post` weakened to `x ≤ 5` no invariant exists, since the counter reaches `10`.
-/

/-- info:
post x ≤ 10 : (lambda ((x Int)) (<= x 10))
post x ≤ 5  : no invariant
-/
#guard_msgs in #eval Env.runIO do
  let report (bound : Int) : Env Unit := do
    let s ← Solver.new
    s.setOption "sygus" "true"
    let int ← Srt.int
    let bool ← Srt.bool
    let x ← BVar.mk int "x"
    let x' ← BVar.mk int "x'"
    let inv ← s.synthFun "inv" #[x] bool
    let pre ← s.defineFun "pre" #[x] bool (← smt! x = 0)
    let trans ← s.defineFun "trans" #[x, x'] bool (← smt! x < 10 ∧ x' = x + 1)
    let post ← s.defineFun "post" #[x] bool (← smt! x ≤ ![Term.mkInt bound])
    s.addSygusInvConstraint inv pre trans post
    let label := s!"post x ≤ {bound}".pushn ' ' (2 - (toString bound).length)
    s.checkSynth (ifSolved := do println! "{label} : {← s.getSynthSolution inv}")
      (ifUnsolvable := println! "{label} : no invariant")
  report 10
  report 5



/-! ## Giving up

A grammar of sums of `x` cannot express `a + 1`, and cvc5 cannot show it, so it searches until the
time limit and answers unknown. `checkSynth?` defaults only its solved and unsolvable branches, so
it fails there.
-/

/-- info:
isSolved?  : none
checkSynth : unknown branch
checkSynth?: unexpected `unknown` synthesis result
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  s.setOption "tlimit-per" "100"
  let int ← Srt.int
  let x ← BVar.mk int "x"
  let start ← NT.mk int "start"
  let g ← s.mkGrammar #[x] start
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start (← Term.add start.toTerm start.toTerm)
  let f ← s.synthFun "f" #[x] int g
  let a ← s.declareSygusVar "a" int
  s.addSygusConstraint (← smt! f a = a + 1)
  println! "isSolved?  : {← (← s.checkSynthResult).isSolved?}"
  s.checkSynth (ifUnknown := println! "checkSynth : unknown branch")
  try
    let _ ← s.checkSynth? (ifSolved := return some "solved")
    println! "checkSynth?: no error"
  catch e => println! "checkSynth?: {e}"



/-! ## Symbols as sygus variables

`declareSygusIn` declares a symbol structure's fields as the variables a specification quantifies
over, and `declareSygusAtIn` names them for a step.
-/

/-- The two inputs of a function to synthesize. -/
structure.symbols Inputs where
  lft : Int
  rgt : Int

/-- info:
variables : lft rgt
at step 2 : lft__@__2 rgt__@__2
solution  : (lambda ((x Int) (y Int)) (+ y x))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let ids : Inputs.Idents := Symbols.Sig.idents ()
  let i ← ids.declareSygusIn s
  println! "variables : {i.lft} {i.rgt}"
  let i2 ← ids.declareSygusAtIn 2 s
  println! "at step 2 : {i2.lft.get} {i2.rgt.get}"
  let x ← BVar.mk int "x"
  let y ← BVar.mk int "y"
  let f ← s.synthFun "f" #[x, y] int
  s.addSygusConstraint (← smt! f i.lft i.rgt = i.lft + i.rgt)
  s.checkSynth (ifSolved := do println! "solution  : {← s.getSynthSolution f}")
