/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Solver

public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Solver



/-! # Substitution, typed

Simultaneous and applied once, as sort-erased. What the index adds is that a pair's two terms share
it: replacing a sub-term of sort `β` by another of sort `β` cannot change the sort of the whole, so
the result is still a `Term α`. `heteroSubstitute` relaxes that *across* pairs, never within one.
-/
namespace Cvc.Tests.Typed.Subst

open Cvc
open Cvc.Typed (Term Terms Solver)
open Cvc.Typed.Term

/-- Two integers, two Booleans, and the term `b ∧ i < j`. -/
def setup [Ω]
: Env (Term Int × Term Int × Term Bool × Term Bool × Term Bool) := do
  let s ← Solver.new
  let i ← s.declareConst Int "i"
  let j ← s.declareConst Int "j"
  let b ← s.declareConst Bool "b"
  let c ← s.declareConst Bool "c"
  return (i, j, b, c, ← and b (← lt i j))



/-! ## The index survives -/

/-- info:
base   : (and b (< i j))
i ↦ j  : (and b (< j j))
b ↦ c  : (and c (< i j))
hetero : (and c (< j j))
-/
#guard_msgs in #eval Env.runIO do
  let (i, j, b, c, t) ← setup
  println! "base   : {t.erase}"
  -- an `Int` sub-term replaced by an `Int` one, in a `Term Bool`, still a `Term Bool`
  println! "i ↦ j  : {(← t.substitute #[(i, j)]).erase}"
  println! "b ↦ c  : {(← t.substitute #[(b, c)]).erase}"
  -- both at once, at two different indices
  println! "hetero : {(← t.heteroSubstitute #[⟨Int, i, j⟩, ⟨Bool, b, c⟩]).erase}"

/-- info: parallel : (and b (< j j)) -/
#guard_msgs in #eval Env.runIO do
  let (i, j, _b, _c, t) ← setup
  println! "parallel : {(← t.substitute' #[i] #[j]).erase}"

section discipline
variable [Ω] (t : Term Bool) (i j : Term Int) (b : Term Bool)

/-- Substituting preserves the index of the term substituted into. -/
example : Env (Term Bool) := t.substitute #[(i, j)]
/-- …whatever the index of the pair. -/
example : Env (Term Bool) := t.substitute #[(b, b)]

/-- info: @substitute : [inst : Ω] → {α β : Type} → Term α → Array (Term β × Term β) → Env (Term α) -/
#guard_msgs in #check @Cvc.Typed.Term.substitute

-- a pair whose halves disagree is a type error: it could change the term's sort
/-- error: Application type mismatch: The argument
  b
has type
  Term Bool
but is expected to have type
  Term Int
in the application
  (i, b)

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 6
-/
#guard_msgs in example := t.substitute #[(i, b)]

/-- error: could not synthesize default value for parameter 'valid' using tactics
---
error: failed to prove there are as many replacements as sub-terms
inst✝ : Ω
t : Term Bool
i j : Term Int
b : Term Bool
⊢ #[i].size = #[].size
-/
#guard_msgs in
example : Env (Term Bool) := t.substitute' #[i] #[]

end discipline
