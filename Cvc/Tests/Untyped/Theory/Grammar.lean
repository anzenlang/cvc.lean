/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Grammar
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Theory.Grammar
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory



/-! # SyGuS grammars, sort-erased -/
namespace Cvc.Tests.Untyped.Grammar

open Cvc
open Cvc.Untyped



/-! ## Building a grammar

`toString` is the SyGuS pre-declaration followed by the rules, so it is a faithful picture of what
the grammar actually is.
-/

/-- info:
empty   : 
rules   : ((start Int) )((start Int (x 0 (+ start start))))
addRules: ((start Int) )((start Int (0 1 2)))
anyConst: ((start Int) )((start Int ((Constant Int) 0)))
anyVar   : ((start Int) )((start Int (x)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let x ← BVar.mk int "x"
  let start ← NT.mk int "start"

  -- a grammar with no rules yet prints as nothing at all, not even its pre-declaration
  println! "empty   : {← s.mkGrammar #[x] start}"

  -- a non-terminal coerces to a term, which is how it appears inside its own rules
  let g ← s.mkGrammar #[x] start
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start (← Term.mkInt 0)
  let g ← g.addRule start (← Term.add start start)
  println! "rules   : {g}"

  let g ← s.mkGrammar #[] start
  let g ← g.addRules start #[← Term.mkInt 0, ← Term.mkInt 1, ← Term.mkInt 2]
  println! "addRules: {g}"

  println! "anyConst: {← (← s.mkGrammar #[] start).addAnyConstant start}"
  println! "anyVar   : {← (← s.mkGrammar #[x] start).addAnyVariable start}"

-- several non-terminals: the first is the start symbol, so order is meaningful
/-- info: ((start Int) (cnd Bool) )((start Int (0 (ite cnd start start)))(cnd Bool (true))) -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let start ← NT.mk (← Srt.int) "start"
  let cnd ← NT.mk (← Srt.bool) "cnd"

  let g ← s.mkGrammar #[] start #[cnd]
  let g ← g.addRule start (← Term.mkInt 0)
  let g ← g.addRule start (← Term.ite cnd start start)
  let g ← g.addRule cnd (← Term.mkTrue)
  println! "{g}"



/-! ## What is checked when

A non-terminal belongs to one grammar, and a rule must have its non-terminal's sort. Neither shows
in a signature at this layer, so both are caught when the rule is added.
-/

/-- info:
foreign nt : caught
wrong sort : caught
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let start ← NT.mk int "start"
  let stranger ← NT.mk int "stranger"
  let g ← s.mkGrammar #[] start

  let caught (code : Env Grammar) : Env String :=
    try let _ ← code ; pure "no error" catch _ => pure "caught"

  println! "foreign nt : {← caught (g.addRule stranger (← Term.mkInt 0))}"
  println! "wrong sort : {← caught (g.addRule start (← Term.mkTrue))}"

-- the start symbol is an argument of its own, not the head of an array. cvc5 takes the first
-- non-terminal as the start symbol and silently drops whatever is unreachable from it, so an array
-- would let a swapped order produce a grammar missing half its rules and no error at all
section discipline
variable [Ω] (s : Solver) (start cnd : NT)

/-- A grammar always has a start symbol; there is no empty case to reject. -/
example : Env Grammar := s.mkGrammar #[] start

/-- Auxiliary non-terminals are separate, and cannot be mistaken for the start symbol. -/
example : Env Grammar := s.mkGrammar #[] start #[cnd]

/-- info: @Solver.mkGrammar : [inst : Ω] → Solver → BVars → NT → optParam NTs #[] → Env Grammar -/
#guard_msgs in #check @Cvc.Untyped.Solver.mkGrammar

-- a grammar belongs to the scope, not to the solver that built it: another solver takes it
example (s₂ : Solver) (g : Grammar) (conj : Term) : Env (Option Term) :=
  s₂.getInterpolant conj (some g)

end discipline



/-! ## `smt.grammar!`

The block form builds the same grammar as the builders do: the first test is the hand-built one
above, rewritten. A sort is a Lean type or a `Srt`, freely mixed. `?var` is printed as the
parameters it stands for, cvc5 inlining them.
-/

/-- info:
block : ((start Int) (cnd Bool) )((start Int (x y (ite cnd start start)))(cnd Bool ((<= start start))))
any   : ((start Int) )((start Int (0 (Constant Int) x (+ start start))))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let g ← smt.grammar! s (x : Int) (y : int) where
    start : Int  := x | y | if cnd then start else start
    cnd   : Bool := start ≤ start
  println! "block : {g}"
  let g ← smt.grammar! s (x : Int) where
    start : int := 0 | ?const | ?var | start + start
  println! "any   : {g}"

/-! What the expansion refuses, where it is written. -/

/-- error: non-terminal `start` is declared twice -/
#guard_msgs in
example [Ω] (s : Solver) : Env Grammar := smt.grammar! s where
  start : Int := 0
  start : Int := 1

/-- error: expected `?const` or `?var`, got `?foo` -/
#guard_msgs in
example [Ω] (s : Solver) : Env Grammar := smt.grammar! s where
  start : Int := ?foo



/-! ## A grammar is the scope's

cvc5 builds a grammar through a solver, but any solver of the same term manager accepts it: here
`s1` builds it and `s2` interpolates with it, and the grammar's restriction still holds.
-/

/-- info: interpolant from s2 : (< a b) -/
#guard_msgs in #eval Env.runIO do
  let s1 ← Solver.new
  let s2 ← Solver.new
  s2.setOption "produce-interpolants" "true"
  let int ← Srt.int
  let a ← Term.mkSymbol int "a"
  let b ← Term.mkSymbol int "b"
  let g ← smt.grammar! s1 where
    start : Bool := a < b | a = b
  Term.lt a b >>= s2.assert
  let goal ← Term.lt a (← Term.add b (← Term.mkInt 1))
  let some i ← s2.getInterpolant goal g | println! "no interpolant"
  println! "interpolant from s2 : {i}"



/-! ## Extending a grammar after the fact

`smt.mkGrammar!` answers the grammar together with what it was built from, so that rules can be
added afterwards: `grammar × NT₁ × …` without parameters, `(grammar × PARAM₁ × …) × NT₁ × …` with
some — grouped so that a parameter cannot be taken for a non-terminal by position.
`smt.letGrammar! g ← …` binds the same things under the names the block declares.
-/

section parts
variable [Ω] (s : Solver)

/-- Without parameters, the grammar then the non-terminals. -/
example : Env (Grammar × NT) := smt.mkGrammar! s where
  start : Int := 0 | start + start

/-- With parameters, the grammar grouped with them, then the non-terminals. -/
example : Env ((Grammar × BVar × BVar) × NT × NT) := smt.mkGrammar! s (x y : Int) where
  start : Int  := x | y
  cnd   : Bool := start ≤ start

end parts

/-! A non-terminal that nothing reachable from the start symbol mentions is not printed — cvc5
drops what is unreachable — until a rule added afterwards reaches it. Unused bindings, `never`
here, draw no warning. -/

/-- info:
before : ((start Int) )((start Int (x y)))
after  : ((start Int) (cnd Bool) )((start Int (x y (ite cnd start start)))(cnd Bool ((<= start start))))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  smt.letGrammar! g ← s (x y : Int) where
    start : Int  := x | y
    cnd   : Bool := start ≤ start
    never : Int  := 0
  println! "before : {g}"
  let g ← g.addRule start (← smt! if cnd then start else start)
  println! "after  : {g}"

/-! `smt.mkGrammar!` destructured by position, and `smt.letGrammar!` without parameters, where
there is no group to bind: the grammar comes first, then the non-terminals. -/

/-- info:
mk  : ((start Int) )((start Int (x (+ start x))))
let : ((start Int) (cnd Bool) )((start Int (0 (ite cnd 1 start)))(cnd Bool ((<= start start))))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let ((g, x, _), start) ← smt.mkGrammar! s (x y : Int) where
    start : Int := x
  let g ← g.addRule start (← smt! start + x)
  println! "mk  : {g}"
  smt.letGrammar! g ← s where
    start : Int  := 0
    cnd   : Bool := start ≤ start
  let g ← g.addRule start (← smt! if cnd then 1 else start)
  println! "let : {g}"

/-! Extending stops at the freeze: once a solver has used the grammar, cvc5 rejects a new rule. -/

/-- info: [internal] Grammar cannot be modified after passing it as an argument to synthFun
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  smt.letGrammar! g ← s (x : Int) where
    start : Int := x | start + start
  discard <| s.synthFun "f" g.boundVars int g
  try discard <| g.addRule start (← smt! start + 1); println! "no error"
  catch e => println! "{e}"

/-! A non-terminal declared without alternatives, `num : Int` alone, has its rules added afterwards:
here they are computed from a list, which a block cannot spell. Until then it reaches nothing. -/

/-- info:
block : ((start Int) (num Int) )((start Int (x (+ start num)))(num Int ()))
after : ((start Int) (num Int) )((start Int (x (+ start num)))(num Int (3 7)))
f := (lambda ((x Int)) (+ (+ x 3) 7))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let ((g, _), start, num) ← smt.mkGrammar! s (x : Int) where
    start : Int := x | start + num
    num   : Int
  println! "block : {g}"
  let mut g := g
  for k in [3, 7] do
    g ← g.addRule num (← Term.mkInt k)
  println! "after : {g}"
  -- `start` is still extensible, alongside
  g ← g.addRule start (← smt! 2 * start)
  let f ← s.synthFun "f" g.boundVars (← Srt.int) g
  let a ← s.declareSygusVar "a" (← Srt.int)
  s.addSygusConstraint (← smt! f a = a + 10)
  s.checkSynth (ifSolved := do println! "f := {← s.getSynthSolution f}")

/-! `smt.grammar!` refuses a non-terminal without alternatives, the grammar it answers being closed. -/

/-- error: non-terminal `num` has no alternatives, and the grammar `smt.grammar!` answers cannot be extended: give it some, or use `smt.mkGrammar!` or `smt.letGrammar!` to add its rules afterwards -/
#guard_msgs in
example [Ω] (s : Solver) : Env Grammar := smt.grammar! s where
  start : Int := num
  num   : Int
