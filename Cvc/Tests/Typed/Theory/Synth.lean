/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Synth
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Theory.Synth
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # Syntax-guided synthesis, typed -/
namespace Cvc.Tests.Typed.Synth

open Cvc
open Cvc
open Cvc.Typed



/-! ## Synthesizing under a grammar

`synthFun` takes nothing but the grammar: a `Grammar σ` carries the parameters it was built over
and the sort it starts at, so there is no second place for those to come from and disagree. The
result is a `Term σ`, which is why `Term.apply2` below needs no re-typing.
-/

/-- info:
solution : (lambda ((x Int) (y Int)) (ite (<= y x) x y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let x ← BVar.mk (α := Int) "x"
  let y ← BVar.mk (α := Int) "y"
  let params := BVars.push y (BVars.push x [])

  let start ← NT.mk (α := Int) "start"
  let cnd ← NT.mk (α := Bool) "cnd"
  let g ← s.mkGrammar params start (NTs.push cnd [])
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start y.toTerm
  let g ← g.addRule start (← Term.ite cnd.toTerm start.toTerm start.toTerm)
  let g ← g.addRule cnd (← Term.le start.toTerm start.toTerm)

  let mx ← s.synthFun "max" g

  let a ← s.declareSygusVar Int "a"
  let b ← s.declareSygusVar Int "b"
  let mab ← Term.apply2 mx a b
  s.addSygusConstraint (← Term.ge mab a)
  s.addSygusConstraint (← Term.ge mab b)
  s.addSygusConstraint (← Term.or (← Term.equal mab a) (← Term.equal mab b))

  s.checkSynth (ifSolved := do
    println! "solution : {(← s.getSynthSolution mx).erase}")



/-! ## Without a grammar

`synthAnyFun` is the unconstrained form. With no grammar to take a signature from, the parameters
and codomain are given directly and folded into the index the same way.
-/

/-- info:
solution : (lambda ((x Int)) (+ x 1))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let x ← BVar.mk (α := Int) "x"
  let f ← s.synthAnyFun' "f" (BVars.push x []) Int

  let a ← s.declareSygusVar Int "a"
  s.addSygusConstraint (← Term.equal (← Term.apply f a) (← Term.add a (← Term.mkInt 1)))

  s.checkSynth (ifSolved := do
    println! "solution : {(← s.getSynthSolution f).erase}")



/-! ## The indices

A synthesized function's index is its signature, and a solution has the signature of the function
it solves for. Both come from the grammar, so neither is stated at a call site.
-/

section signatures
variable [Ω] (s : Solver) (i : BVar Int) (b : BVar Bool) (nt : NT Int)
  (g : Typed.Grammar (Int → Int)) (f : Term (Int → Int))

example : Env (Term (Int → Int)) := s.synthFun "f" g
-- and a solution can only be read where one was found, which is what `EnvSolved` records
example : EnvSolved (Term (Int → Int)) := s.getSynthSolution f

example : Env (Term Int) := s.synthAnyFun' "f" [] Int
example : Env (Term (Int → Int)) := s.synthAnyFun' "f" (BVars.push i []) Int
example : Env (Term (Int → Bool → Int)) := s.synthAnyFun' "f" (BVars.push b (BVars.push i [])) Int

/-- info: @Solver.synthFun : [inst : Ω] → Solver → {σ : Type} → String → Typed.Grammar σ → Env (Term σ) -/
#guard_msgs in #check @Cvc.Typed.Solver.synthFun

/-- info: @Solver.getSynthSolution : [inst : Ω] → Solver → {σ : Type} → Term σ → EnvSolved (Term σ) -/
#guard_msgs in #check @Cvc.Typed.Solver.getSynthSolution

-- a constraint is a formula, so it takes `Term Bool` and nothing else
/-- info: @Solver.addSygusConstraint : [inst : Ω] → Solver → Term Bool → Env Unit -/
#guard_msgs in #check @Cvc.Typed.Solver.addSygusConstraint

end signatures



/-! ## No solution -/

/-- info: branch : unsolvable -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let x ← BVar.mk (α := Int) "x"
  let y ← BVar.mk (α := Int) "y"
  let params := BVars.push y (BVars.push x [])

  let start ← NT.mk (α := Int) "start"
  let g ← s.mkGrammar params start
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start y.toTerm

  -- only the two projections are allowed, and neither is a `max`
  let mx ← s.synthFun "max" g
  let a ← s.declareSygusVar Int "a"
  let b ← s.declareSygusVar Int "b"
  let mab ← Term.apply2 mx a b
  s.addSygusConstraint (← Term.ge mab a)
  s.addSygusConstraint (← Term.ge mab b)

  s.checkSynth (ifUnsolvable := do println! "branch : unsolvable")
