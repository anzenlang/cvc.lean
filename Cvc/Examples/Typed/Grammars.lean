/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed

public meta import Cvc.Typed



/-! # Grammars, typed

The same grammars as the sort-erased demo, with the index doing two jobs that are worth seeing
side by side.

**A rule's sort cannot disagree with its non-terminal's.** Sort-erased that is a runtime error out
of cvc5; here `addRule` takes a `Term α` at the non-terminal's own index, so it does not compile.

**A `Grammar σ` carries the signature it generates** — the parameters it was built over, folded
with the start symbol's sort. That is why `synthFun` takes *nothing but the grammar*: there is no
second place for the parameters to come from and disagree, and the solution comes back at the
function's own index.

What stays a runtime check is what a type here cannot state: that a non-terminal belongs to *this*
grammar, which is a property of a value.
-/
namespace Cvc.Examples.Typed.Grammars

open Cvc Typed

variable [Ω]



/-! ## Building one

Parameters are collected in a `BVars` spine and non-terminals in `NTs`, so neither can come out
empty by accident and the start symbol is named separately from the rest.
-/

/-- info: ((start Int) (cnd Bool) )((start Int (x y (ite cnd start start)))(cnd Bool ((<= start start))))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let x ← BVar.mk (α := Int) "x"
  let y ← BVar.mk (α := Int) "y"
  let start ← NT.mk (α := Int) "start"
  let cnd ← NT.mk (α := Bool) "cnd"

  let bVars := BVars.empty.push x |>.push y
  let g ← s.mkGrammar bVars start (NTs.push cnd [])
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start y.toTerm
  let g ← g.addRule start (← Term.ite cnd.toTerm start.toTerm start.toTerm)
  let g ← g.addRule cnd (← Term.le start.toTerm start.toTerm)
  println! "{g}"

/-! A rule at the wrong sort does not compile. The `cnd` non-terminal is `Bool`, so an `Int` rule
for it is caught where it is written. -/

/--
error: Application type mismatch: The argument
  start.toTerm
has type
  Term Int
but is expected to have type
  Term Bool
in the application
  g.addRule cnd start.toTerm

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example (g : Typed.Grammar σ) (cnd : NT Bool) (start : NT Int) : Env (Typed.Grammar σ) :=
  g.addRule cnd start.toTerm



/-! ## Handing one to the solver

`synthFun` takes the grammar and nothing else, and answers a `Term σ` — so applying the synthesized
function is ordinary typed application, with no re-typing anywhere.
-/

/-- info: max := (lambda ((x Int) (y Int)) (ite (<= y x) x y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let x ← BVar.mk (α := Int) "x"
  let y ← BVar.mk (α := Int) "y"
  let start ← NT.mk (α := Int) "start"
  let cnd ← NT.mk (α := Bool) "cnd"

  let g ← s.mkGrammar (BVars.push y (BVars.push x [])) start (NTs.push cnd [])
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start y.toTerm
  let g ← g.addRule start (← Term.ite cnd.toTerm start.toTerm start.toTerm)
  let g ← g.addRule cnd (← Term.le start.toTerm start.toTerm)

  -- `max : Term (Int → Int → Int)`, the signature the grammar already carried
  let mx ← s.synthFun "max" g

  let a ← s.declareSygusVar Int "a"
  let b ← s.declareSygusVar Int "b"
  let mab ← smt! mx a b
  s.addSygusConstraint (← smt! mab ≥ a)
  s.addSygusConstraint (← smt! mab ≥ b)
  s.addSygusConstraint (← smt! mab = a ∨ mab = b)

  s.checkSynth (ifSolved := do
    println! "max := {(← s.getSynthSolution mx).erase}")

/-! Without a grammar, `synthAnyFun` folds the parameters and the codomain into the index itself,
so the result is indexed just the same. -/

/-- info: f := (lambda ((x Int)) (+ x 1))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let x ← BVar.mk (α := Int) "x"
  let f ← s.synthAnyFun (α := Int) "f" (BVars.push x [])

  let a ← s.declareSygusVar Int "a"
  s.addSygusConstraint (← smt! f a = a + 1)

  s.checkSynth (ifSolved := do
    println! "f := {(← s.getSynthSolution f).erase}")
