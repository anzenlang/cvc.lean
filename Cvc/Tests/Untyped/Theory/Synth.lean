/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Synth
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Theory.Synth
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
