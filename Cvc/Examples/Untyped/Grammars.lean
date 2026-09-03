/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped

public meta import Cvc.Untyped



/-! # Grammars, sort-erased

A grammar restricts the *shape* of a term the solver may produce — the candidates a `synth-fun`
may return, or an interpolant. It is built from non-terminals and rules, and then handed to
whichever solver query should be restricted by it.

Two things about grammars are worth knowing before writing one:

- **the start symbol is named separately**, `mkGrammar boundVars start others`, rather than being
  the head of one array. cvc5 treats the first non-terminal as the start symbol and then silently
  drops whatever is unreachable from it, so passing them in the wrong order yields a grammar
  containing neither the start symbol nor its rules, with no error at all;
- **a grammar freezes once used.** The rule builders answer a new `Grammar`, so the API reads as
  though grammars were persistent, but the object underneath is shared: after `synthFun`, cvc5
  rejects further rules.
-/
namespace Cvc.Examples.Untyped.Grammars

open Cvc Untyped

variable [Ω]



/-! ## Building one

`toString` on a grammar is its SyGuS pre-declaration followed by its rules, so it is a faithful
picture of what was built rather than of what was asked for.
-/

/-- info: ((start Int) (cnd Bool) )((start Int (x y (ite cnd start start)))(cnd Bool ((<= start start))))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let bool ← Srt.bool

  -- the parameters the generated term may mention…
  let x ← BVar.mk int "x"
  let y ← BVar.mk int "y"
  -- …and the non-terminals it is built from
  let start ← NT.mk int "start"
  let cnd ← NT.mk bool "cnd"

  let g ← s.mkGrammar #[x, y] start #[cnd]
  -- a non-terminal is a term, which is how it appears inside its own rules
  let g ← g.addRules start #[x.toTerm, y.toTerm]
  let g ← g.addRule start (← Term.ite cnd start start)
  let g ← g.addRule cnd (← Term.le start start)
  println! "{g}"

/-! Two shorthands stand in for whole families of rules: any constant of the non-terminal's sort,
and any of the grammar's own parameters. -/

/-- info: ((start Int) )((start Int ((Constant Int) x)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let x ← BVar.mk (← Srt.int) "x"
  let start ← NT.mk (← Srt.int) "start"

  let g ← s.mkGrammar #[x] start
  let g ← g.addAnyConstant start
  let g ← g.addAnyVariable start
  println! "{g}"



/-! ## Handing one to the solver

`synthFun` asks for a function satisfying its constraints *for every input*, where `checkSat` asks
whether constraints can be satisfied at all. With a grammar, the answer is restricted to terms the
grammar can produce — which is what makes the solution below an `ite` and not, say, an arithmetic
expression that happens to agree.

`checkSynth` splits the world as `checkSat` does, and `getSynthSolution` exists only in the branch
where a solution was found.
-/

/-- info: max := (lambda ((x Int) (y Int)) (ite (<= y x) x y))
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
  let g ← g.addRules start #[x.toTerm, y.toTerm]
  let g ← g.addRule start (← Term.ite cnd start start)
  let g ← g.addRule cnd (← Term.le start start)

  -- the function to find, restricted to what the grammar generates
  let mx ← s.synthFun "max" #[x, y] int g

  -- its specification, over universally quantified inputs
  let a ← s.declareSygusVar "a" int
  let b ← s.declareSygusVar "b" int
  let mab ← smt! mx a b
  s.addSygusConstraint (← smt! mab ≥ a)
  s.addSygusConstraint (← smt! mab ≥ b)
  s.addSygusConstraint (← smt! mab = a ∨ mab = b)

  s.checkSynth (ifSolved := do
    println! "max := {← s.getSynthSolution mx}")

/-! Without a grammar, `synthFun` allows any term of the right sort — the same specification is
solved, but the shape of the answer is the solver's to choose. -/

/-- info: f := (lambda ((x Int)) (+ x 1))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let x ← BVar.mk int "x"

  let f ← s.synthFun "f" #[x] int
  let a ← s.declareSygusVar "a" int
  s.addSygusConstraint (← smt! f a = a + 1)

  s.checkSynth (ifSolved := do
    println! "f := {← s.getSynthSolution f}")
