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
namespace Cvc.Typed.Examples.Grammars variable [Ω]

open Cvc Typed



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
  Grammar.addRule g cnd start.toTerm

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example (s : Solver) (g : s.Grammar σ) (cnd : NT Bool) (start : NT Int) : Env (s.Grammar σ) :=
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



/-! ## Writing one as a block

`grammar!` writes a grammar BNF-style, its alternatives in `smt!` syntax: the solver, the
parameters, then one line per non-terminal, the first being the start symbol. Inside the rules a
non-terminal or a parameter stands for its term. This is the `max` grammar above again, and its
index is the same `Int → Int → Int`.
-/

/-- info: max := (lambda ((x Int) (y Int)) (ite (<= y x) x y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let g ← grammar! s (x y : Int) where
    start : Int  := x | y | if cnd then start else start
    cnd   : Bool := start ≤ start

  let mx ← s.synthFun "max" g
  let a ← s.declareSygusVar Int "a"
  let b ← s.declareSygusVar Int "b"
  let mab ← smt! mx a b
  s.addSygusConstraint (← smt! mab ≥ a)
  s.addSygusConstraint (← smt! mab ≥ b)
  s.addSygusConstraint (← smt! mab = a ∨ mab = b)

  s.checkSynth (ifSolved := do
    println! "max := {(← s.getSynthSolution mx).erase}")



/-! ## Interpolation under a grammar

An interpolant of assertions `A` and a goal `C` is a formula over the symbols they share such that
`A → I` and `I → C`. A grammar restricts *how* it may say so, which is a way of asking for an
explanation in a given vocabulary.

Here `A` is `y = 6x + 3` with `x ≥ 0`, and `C` is `y ≠ 5 ∧ y ≠ 6`, so `y` is the only shared
symbol. Left to itself cvc5 answers with a case split on the value of `y`. Restricted to
conjunctions of remainder facts `y % k = r` it has to find the arithmetic reason instead — and no
single fact will do, `5` being odd but not a multiple of 3 and `6` a multiple of 3 but even.
-/

/-- Whether `hyps` entail `concl`, by refuting `hyps ∧ ¬concl` on a fresh solver. -/
def entails (hyps : Array (Term Bool)) (concl : Term Bool) : Env Bool := do
  let s ← Solver.new
  for h in hyps do s.assert h
  Term.not concl >>= s.assert
  return !(← s.checkIsSat)

/-- info:
free        : (= y (ite (<= y 6) 3 y))
constrained : (and (= (mod y 2) 1) (= (mod y 3) 0))
A → I       : true
I → C       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let x ← s.declareConst Int "x"
  let y ← s.declareConst Int "y"
  let hyps := #[← smt! y = 6 * x + 3, ← smt! x ≥ 0]
  for h in hyps do s.assert h
  let goal ← smt! ¬ (y = 5) ∧ ¬ (y = 6)

  if let some i ← s.getInterpolant goal then println! "free        : {i}"

  let g ← grammar! s where
    start : Bool := atom | atom ∧ start
    atom  : Bool := y % k = r
    k     : Int  := 2 | 3 | 4 | 5
    r     : Int  := 0 | 1 | 2

  let some i ← s.getInterpolant goal g | println! "no interpolant"
  println! "constrained : {i}"
  println! "A → I       : {← entails hyps i}"
  println! "I → C       : {← entails #[i] goal}"
