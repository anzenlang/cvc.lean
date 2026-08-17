/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Grammar
import Cvc.Typed.Solver
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Theory.Grammar
public meta import Cvc.Typed.Solver
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # SyGuS grammars, typed -/
namespace Cvc.Tests.Typed.Grammar

open Cvc
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

example : Env (Typed.Grammar Int) := s.mkGrammar [] nt
example : Env (Typed.Grammar (Int → Int)) := s.mkGrammar (BVars.push i []) nt
example : Env (Typed.Grammar (Int → Bool → Int)) := s.mkGrammar (BVars.push b (BVars.push i [])) nt
example : Env (Typed.Grammar Bool) := s.mkGrammar [] ntB

/-- info: @Solver.mkGrammar : [inst : Ω] →
  Solver →
    {α : Type} →
      [ToTyp α] → (boundVars : BVars) → NT α → optParam NTs [] → Env (Typed.Grammar (BVars.signatureTo α boundVars)) -/
#guard_msgs in #check @Cvc.Typed.Solver.mkGrammar

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
example [Ω] (g : Typed.Grammar Int) (nt : NT Int) (tru : Term Bool) : Env (Typed.Grammar Int) :=
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

  let a ← s.declareConst Int "a"
  let b ← s.declareConst Int "b"
  (do Term.lt a b) >>= s.assert
  let goal ← Term.lt a (← Term.add b (← Term.mkInt 1))

  println! "no grammar : {← s.getInterpolant goal}"

  let start ← NT.mk (α := Bool) "start"
  let g ← s.mkGrammar [] start
  let g ← g.addRule start (← Term.lt a b)
  let g ← g.addRule start (← Term.equal a b)
  println! "constrained: {← s.getInterpolant goal g}"
