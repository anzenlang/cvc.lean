/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Grammar
import Cvc.Typed.Synth
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Grammar
public meta import Cvc.Typed.Synth
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # SyGuS grammars, typed -/
namespace Cvc.Tests.Typed.Grammar

open Cvc
open Cvc.Typed



/-! ## Building a grammar -/

/-- info:
rules : ((start Int) )((start Int (x 0 (+ start start))))
ite   : ((start Int) (cnd Bool) )((start Int (0 (ite cnd start start)))(cnd Bool (true)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let x ← BVar.mk (α := Int) "x"
  let start ← NT.mk (α := Int) "start"
  let g ← s.mkGrammar (BVars.push x []) start
  -- a non-terminal coerces to a term, which is how it appears inside its own rules
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start (← Term.mkInt 0)
  let g ← g.addRule start (← Term.add start start)
  println! "rules : {g}"

  -- a second non-terminal at another sort, passed through `others`
  let cnd ← NT.mk (α := Bool) "cnd"
  let g ← s.mkGrammar [] start (NTs.push cnd [])
  let g ← g.addRule start (← Term.mkInt 0)
  let g ← g.addRule start (← Term.ite cnd start start)
  let g ← g.addRule cnd (← Term.mkTrue)
  println! "ite   : {g}"



/-! ## The index is the signature the grammar generates

`mkGrammar` folds its parameters and the start symbol's sort exactly as `Solver.defineFun` folds
its own, so a grammar's index says what a `synth-fun` over it would produce. With no parameters
that is just the start sort, which is the shape `getInterpolant` and `getAbduct` ask for.
-/

section signatures
variable [Ω] (s : Solver) (i : BVar Int) (b : BVar Bool) (nt : NT Int) (ntB : NT Bool)

example : Env (Grammar Int) := s.mkGrammar [] nt
example : Env (Grammar (Int → Int)) := s.mkGrammar (BVars.push i []) nt
example : Env (Grammar (Int → Bool → Int)) := s.mkGrammar (BVars.push b (BVars.push i [])) nt
example : Env (Grammar Bool) := s.mkGrammar [] ntB

/-- info: @Solver.mkGrammar : [inst : Ω] →
  Solver →
    {α : Type} →
      [ToTyp α] → (boundVars : BVars) → NT α → optParam NTs [] → Env (Grammar (BVars.signatureTo α boundVars)) -/
#guard_msgs in #check @Cvc.Typed.Solver.mkGrammar

-- a grammar belongs to the scope, not to the solver that built it: another solver takes it
example (s₂ : Solver) (g : Grammar Bool) (conj : Term Bool) : Env (Option (Term Bool)) :=
  s₂.getInterpolant conj (some g)

end signatures



/-! ## What the types rule out

A rule must have its non-terminal's sort — sort-erased that is a runtime error, here it does not
typecheck. That a non-terminal belongs to *this* grammar is a property of a value, not a type, so
it stays a runtime check in both layers.
-/

/-- error: Application type mismatch: The argument
  tru
has type
  Term Bool
but is expected to have type
  Term Int
in the application
  g.addRule nt tru

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4 -/
#guard_msgs in
example [Ω] (s : Solver) (g : Grammar Int) (nt : NT Int) (tru : Term Bool)
: Env (Grammar Int) :=
  g.addRule nt tru

/-- info: foreign nt : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let start ← NT.mk (α := Int) "start"
  let stranger ← NT.mk (α := Int) "stranger"
  let g ← s.mkGrammar [] start

  let outcome ←
    try
      let _ ← g.addRule stranger (← Term.mkInt 0)
      pure "no error"
    catch _ => pure "caught"
  println! "foreign nt : {outcome}"

-- a non-terminal is not a parameter: `mkGrammar` takes them separately and only the types keep
-- them apart, which is the point of `NT` being its own type
/-- error: Application type mismatch: The argument
  nt
has type
  NT Int
but is expected to have type
  BVar ?m.4
in the application
  BVars.push nt

Note: The following definitions were not unfolded because their definition is not exposed:
  BVar ↦ 2 -/
#guard_msgs in
example [Ω] (nt : NT Int) : BVars := BVars.push nt []



/-! ## End to end

An interpolant under a grammar: the grammar admits only conjunctions of the two comparisons, so
this pins that a grammar actually constrains what comes back.
-/

/-- info:
no grammar : (let ((_let_1 (+ b 1))) (and (<= a _let_1) (not (= a _let_1))))
constrained: (< a b)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let a ← s.declareConstAs Int "a"
  let b ← s.declareConstAs Int "b"
  Term.lt a b >>= s.assert
  let goal ← Term.lt a (← Term.add b (← Term.mkInt 1))

  let some free ← s.getInterpolant goal | println! "no interpolant"
  println! "no grammar : {free}"

  let start ← NT.mk (α := Bool) "start"
  let g ← s.mkGrammar [] start
  let g ← g.addRule start (← Term.lt a b)
  let g ← g.addRule start (← Term.equal a b)
  let some constrained ← s.getInterpolant goal g | println! "no interpolant"
  println! "constrained: {constrained}"



/-! ## `smt.grammar!`

The block form builds the same grammar as `mkGrammar` and the builders, with the same index: the
parameters folded over the start symbol's sort.
-/

/-- info:
block : ((start Int) (cnd Bool) )((start Int (x y (ite cnd start start)))(cnd Bool ((<= start start))))
any   : ((start Int) )((start Int (0 (Constant Int) x (+ start start))))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let g ← smt.grammar! s (x y : Int) where
    start : Int  := x | y | if cnd then start else start
    cnd   : Bool := start ≤ start
  println! "block : {g}"
  let g ← smt.grammar! s (x : Int) where
    start : Int := 0 | ?const | ?var | start + start
  println! "any   : {g}"

section indices
variable [Ω] (s : Solver)

/-- With parameters, the index is the signature a `synth-fun` over the grammar has. -/
example : Env (Grammar (Int → Bool → Int)) := smt.grammar! s (x : Int) (b : Bool) where
  start : Int := x | if b then start else start
/-- Without, it is the start sort, which is what interpolants and abducts ask for. -/
example : Env (Grammar Bool) := smt.grammar! s where
  start : Bool := true | false

end indices

/-! An alternative at the wrong sort is reported at that alternative. -/

/--
error: Type mismatch
  Term.mkTrue
has type
  Env (Term Bool)
but is expected to have type
  Env (Term Int)

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 6
-/
#guard_msgs in
example [Ω] (s : Solver) : Env (Grammar Int) := smt.grammar! s where
  start : Int := 0 | true

/-! The interpolation of the remainders example, with the grammar written as a block: no single
remainder fact rules out both 5 and 6, so the interpolant is a conjunction. -/

/-- info: interpolant : (and (= (mod y 2) 1) (= (mod y 3) 0)) -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  smt! y = 6 * x + 3 >>= s.assert
  smt! x ≥ 0 >>= s.assert
  let g ← smt.grammar! s where
    start : Bool := atom | atom ∧ start
    atom  : Bool := y % k = r
    k     : Int  := 2 | 3 | 4 | 5
    r     : Int  := 0 | 1 | 2
  let some i ← s.getInterpolant (← smt! ¬ (y = 5) ∧ ¬ (y = 6)) g | println! "no interpolant"
  println! "interpolant : {i}"



/-! ## A grammar is the scope's

Built through one solver, used by another: the grammar's restriction still holds.
-/

/-- info: interpolant from s2 : (< a b) -/
#guard_msgs in #eval Env.runIO do
  let s1 ← Solver.new
  let s2 ← Solver.new
  s2.setOption "produce-interpolants" "true"
  let a ← Term.mkSymbolAs Int "a"
  let b ← Term.mkSymbolAs Int "b"
  let g ← smt.grammar! s1 where
    start : Bool := a < b | a = b
  smt! a < b >>= s2.assert
  let some i ← s2.getInterpolant (← smt! a < b + 1) g | println! "no interpolant"
  println! "interpolant from s2 : {i}"



/-! ## Extending a grammar after the fact

`smt.mkGrammar!` answers the grammar together with what it was built from, at their indices:
`Grammar σ × NT α₁ × …` without parameters, `(Grammar σ × BVar β₁ × …) × NT α₁ × …` with some.
`smt.letGrammar! g ← …` binds the same things under the names the block declares.
-/

section parts
variable [Ω] (s : Solver)

/-- Without parameters, the grammar then the non-terminals. -/
example : Env (Grammar Int × NT Int) := smt.mkGrammar! s where
  start : Int := 0 | start + start

/-- With parameters, the grammar grouped with them, then the non-terminals. -/
example : Env ((Grammar (Int → Int → Int) × BVar Int × BVar Int) × NT Int × NT Bool) :=
  smt.mkGrammar! s (x y : Int) where
    start : Int  := x | y
    cnd   : Bool := start ≤ start

end parts

/-! A grammar extended after `smt.letGrammar!`, then used for synthesis. -/

/-- info:
after : ((start Int) (cnd Bool) )((start Int (x y (ite cnd start start)))(cnd Bool ((<= start start))))
max := (lambda ((x Int) (y Int)) (ite (<= y x) x y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  smt.letGrammar! g ← s (x y : Int) where
    start : Int  := x | y
    cnd   : Bool := start ≤ start
  let g ← g.addRule start (← smt! if cnd then start else start)
  println! "after : {g}"
  let mx ← s.synthFun "max" g
  let a ← s.declareSygusVar Int "a"
  let b ← s.declareSygusVar Int "b"
  let mab ← smt! mx a b
  s.addSygusConstraint (← smt! mab ≥ a)
  s.addSygusConstraint (← smt! mab ≥ b)
  s.addSygusConstraint (← smt! mab = a ∨ mab = b)
  s.checkSynth (ifSolved := do println! "max := {(← s.getSynthSolution mx).relax}")

/-! A parameter is not a non-terminal: extending a grammar "at" one does not compile. -/

/--
error: Application type mismatch: The argument
  x
has type
  BVar Int
but is expected to have type
  NT ?m.99
in the application
  g.addRule x

Note: The following definitions were not unfolded because their definition is not exposed:
  BVar ↦ 2
-/
#guard_msgs in
example [Ω] (s : Solver) : Env Unit := do
  smt.letGrammar! g ← s (x : Int) where
    start : Int := x
  discard <| g.addRule x (← smt! x + 1)

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
  smt.letGrammar! g ← s (x : Int) where
    start : Int := x | start + start
  discard <| s.synthFun "f" g
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
  g ← g.addRule start (← smt! num * start)
  let f ← s.synthFun "f" g
  let a ← s.declareSygusVar Int "a"
  s.addSygusConstraint (← smt! f a = a + 10)
  s.checkSynth (ifSolved := do println! "f := {(← s.getSynthSolution f).relax}")

/-! `smt.grammar!` refuses a non-terminal without alternatives, the grammar it answers being closed. -/

/-- error: non-terminal `num` has no alternatives, and the grammar `smt.grammar!` answers cannot be extended: give it some, or use `smt.mkGrammar!` or `smt.letGrammar!` to add its rules afterwards -/
#guard_msgs in
example [Ω] (s : Solver) : Env (Grammar Int) := smt.grammar! s where
  start : Int := num
  num   : Int

/-! Outside a block, `smt!` converts a non-terminal or a bound variable to its term by its own type,
so operands that are all non-terminals or parameters need nothing else to fix their index — a rule
is usually built that way, inside `(← …)` where there is no expected type. -/

section outside
variable [Ω] (n m : NT Int) (x : BVar Int) (b : NT Bool)

example : Env Unit := do let _ ← smt! n * m
example : Env Unit := do let _ ← smt! n + x
example : Env Unit := do let _ ← smt! n ≤ m
example : Env Unit := do let _ ← smt! if b then n else x

/-! A sort mismatch is still reported between the two terms, with no conversion in the message. -/

/--
error: Application type mismatch: The argument
  smtArg1✝
has type
  Term Bool
but is expected to have type
  Term Int
in the application
  smtArg0✝.add smtArg1✝

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 6
-/
#guard_msgs in
example (t : Term Bool) : Env (Term Int) := smt! n + t

end outside



/-! ## From a sort-erased grammar

`Untyped.Grammar.typeCheckAs` types a grammar built sort-erased, checking the signature against what
the grammar generates, and `Untyped.NT.typeCheckAs` does the same for its non-terminals, so the
grammar can be extended and used through the typed API. -/

/-- info:
typed : ((start Int) (cnd Bool) )((start Int (x y (ite cnd start start)))(cnd Bool ((<= start start))))
max := (lambda ((x Int) (y Int)) (ite (<= y x) x y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let x ← Untyped.BVar.mk int "x"
  let y ← Untyped.BVar.mk int "y"
  let start ← Untyped.NT.mk int "start"
  let cnd ← Untyped.NT.mk (← Srt.bool) "cnd"
  let ug ← Untyped.Grammar.mk #[x, y] start #[cnd]
  let ug ← ug.addRules start #[x.toTerm, y.toTerm]
  let ug ← ug.addRule cnd (← Untyped.Term.le start.toTerm start.toTerm)
  -- typed from here on
  let g ← ug.typeCheckAs (Int → Int → Int)
  let start ← start.typeCheckAs Int
  let cnd ← cnd.typeCheckAs Bool
  let g ← g.addRule start (← smt! if cnd then start else start)
  println! "typed : {g}"
  let mx ← s.synthFun "max" g
  let a ← s.declareSygusVar Int "a"
  let b ← s.declareSygusVar Int "b"
  let mab ← smt! mx a b
  s.addSygusConstraint (← smt! mab ≥ a)
  s.addSygusConstraint (← smt! mab ≥ b)
  s.addSygusConstraint (← smt! mab = a ∨ mab = b)
  s.checkSynth (ifSolved := do println! "max := {(← s.getSynthSolution mx).relax}")

/-! A grammar with no parameters types at its start symbol's sort. A wrong signature — a wrong
parameter count, a wrong codomain, or parameters for a grammar that has none — is refused, as is a
non-terminal at the wrong sort. -/

/-- info:
no params : Grammar Bool
wrong arity:
cannot type the following grammar as `(-> Int Int)`, it generates `(-> Int Int Int)`:
((start Int) )((start Int (x y)))
wrong codomain:
cannot type the following grammar as `(-> Int Int Bool)`, it generates `(-> Int Int Int)`:
((start Int) )((start Int (x y)))
no parameters:
cannot type the following grammar as `(-> Int Bool)`, it generates `Bool`:
((start Bool) )((start Bool (true)))
non-terminal:
cannot type non-terminal `start` as `Bool`, it has sort `Int`
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let x ← Untyped.BVar.mk int "x"
  let y ← Untyped.BVar.mk int "y"
  let start ← Untyped.NT.mk int "start"
  let g ← Untyped.Grammar.mk #[x, y] start
  let g ← g.addRules start #[x.toTerm, y.toTerm]
  let p ← Untyped.NT.mk bool "start"
  let gp ← Untyped.Grammar.mk #[] p
  let gp ← gp.addRule p (← Untyped.Term.mkBool true)
  let _ : Grammar Bool ← gp.typeCheck
  println! "no params : Grammar Bool"
  try discard <| g.typeCheckAs (Int → Int)
  catch e => println! "wrong arity:\n{e}"
  try discard <| g.typeCheckAs (Int → Int → Bool)
  catch e => println! "wrong codomain:\n{e}"
  try discard <| gp.typeCheckAs (Int → Bool)
  catch e => println! "no parameters:\n{e}"
  try discard <| start.typeCheckAs Bool
  catch e => println! "non-terminal:\n{e}"



/-! ## To a sort-erased grammar

`Grammar.relax` is the other direction, and it cannot fail: the typed grammar wraps a sort-erased
one, which carries its own parameters and start sort, so it serves the sort-erased `synthFun` as
is. A round trip through `typeCheckAs` gives the grammar back, and the two views share one cvc5
grammar, so a rule added through the sort-erased one shows in the typed one. -/

/-- info:
relaxed    : ((start Int) )((start Int (x y)))
parameters : #[x, y]
start sort : Int
round trip : ((start Int) )((start Int (x y)))
shared     : ((start Int) )((start Int (x y 0)))
f := (lambda ((x Int) (y Int)) y)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let x ← BVar.mk (α := Int) "x"
  let y ← BVar.mk (α := Int) "y"
  let start ← NT.mk' Int "start"
  let g ← s.mkGrammar (.push y (.push x [])) start
  let g ← g.addRules start #[x.toTerm, y.toTerm]
  let ug := g.relax
  println! "relaxed    : {ug}"
  println! "parameters : {ug.boundVars}"
  println! "start sort : {ug.startSrt}"
  let g' ← ug.typeCheckAs (Int → Int → Int)
  println! "round trip : {g'}"
  discard <| ug.addRule start.relax (← Untyped.Term.mkInt 0)
  println! "shared     : {g}"
  -- the sort-erased `synthFun` takes the relaxed grammar's own parameters and start sort
  let f ← Untyped.Solver.synthFun s "f" ug.boundVars ug.startSrt ug
  let a ← Untyped.Solver.declareSygusVar s "a" (← Srt.int)
  let b ← Untyped.Solver.declareSygusVar s "b" (← Srt.int)
  Untyped.Solver.addSygusConstraint s
    (← Untyped.Term.equal (← Untyped.Term.apply2 f a b) b)
  Untyped.Solver.checkSynth s (ifSolved := do
    println! "f := {← Untyped.Solver.getSynthSolution s f}")
