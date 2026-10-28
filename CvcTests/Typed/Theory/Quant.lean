/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Quant
import Cvc.Typed.Theory.Arith
import Cvc.Typed.Core.Solver

public meta import Cvc.Typed.Theory.Quant
public meta import Cvc.Typed.Theory.Arith
public meta import Cvc.Typed.Core.Solver



/-! # Quantifiers, typed

The same formulas as sort-erased. What the index adds is that a body is a `Term Bool` and each
variable's sort comes from its argument's type, so the sort-erased arity check becomes a type
error, as does a quantifier binding nothing.
-/
namespace Cvc.Tests.Typed.Term.Quant

open Cvc
open Cvc.Typed

/-! ## Construction -/

/-- info:
forall  : (forall ((x Int) (y Int)) (= (+ x y) (+ y x)))
exists  : (exists ((x Int)) (> x y))
forallH : (forall ((x Int) (y Int)) (= (+ x y) (+ y x)))
existsH : (exists ((x Int)) (> x y))
default : (exists ((x0 Int) (x1 Bool)) (and x1 (> x0 y)))
-/
#guard_msgs in #eval Env.runIO do
  let y ← Term.mkSymbolAs Int "y"

  let x ← BVar.mk (α := Int) "x"
  let x' ← BVar.mk (α := Int) "y"
  let comm ← smt! ![pure x.toTerm] + ![pure x'.toTerm] = ![pure x'.toTerm] + ![pure x.toTerm]
  println! "forall  : {← Term.mkForall (BVars.push x' (BVars.push x [])) comm}"
  println! "exists  : {← Term.mkExists (BVars.push x []) (← smt! ![pure x.toTerm] > y)}"

  let comm ← Term.forallH (names := ["x", "y"]) fun (x y : Term Int) => smt! x + y = y + x
  println! "forallH : {comm}"
  println! "existsH : {← Term.existsH (names := ["x"]) fun (x : Term Int) => smt! x > y}"
  -- unnamed variables are named after their position
  let mixed ← Term.existsH fun (x : Term Int) (b : Term Bool) => smt! b ∧ x > y
  println! "default : {mixed}"

/-! A quantifier binding nothing does not typecheck, in either spelling. -/

/--
error: could not synthesize default value for parameter '_nonEmpty' using tactics
---
error: failed to prove a quantifier binds at least one variable
inst✝ : Ω
body : Term Bool
⊢ False
-/
#guard_msgs in
example [Ω] (body : Term Bool) : Env (Term Bool) := Term.mkForall [] body

/--
error: failed to synthesize instance of type class
  Term.Binder (Env (Term Bool))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Ω] (body : Term Bool) : Env (Term Bool) := Term.forallH (pure body : Env (Term Bool))

/-! And the body must be a formula: a body at any other index has no `Binder` instance. -/

/--
error: failed to synthesize instance of type class
  Term.Binder (Term Int → Env (Term Int))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Ω] : Env (Term Bool) := Term.forallH fun (x : Term Int) => smt! x + 1



/-! ## Solving -/

/-- info:
∀ x, x + y = y + x : sat
∀ x, x > y         : unsat
∃ x, x > y         : sat
-/
#guard_msgs in #eval Env.runIO do
  let check (name : String) (f : Term Int → Env (Term Bool)) : Env Unit := do
    let s ← Solver.new
    let y ← s.declareConstAs Int "y"
    s.assert (← f y)
    println! "{name} : {if ← s.checkIsSat then "sat" else "unsat"}"
  check "∀ x, x + y = y + x" fun y => Term.forallH fun (x : Term Int) => smt! x + y = y + x
  check "∀ x, x > y        " fun y => Term.forallH fun (x : Term Int) => smt! x > y
  check "∃ x, x > y        " fun y => Term.existsH fun (x : Term Int) => smt! x > y



/-! ## Quantifier elimination -/

/--
info:
q          : (exists ((x0 Int)) (and (< y x0) (< x0 3)))
qe         : (not (>= y 2))
qeDisjunct : (some (not (>= y 2)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let y ← s.declareConstAs Int "y"
  let q ← Term.existsH fun (x : Term Int) => smt! y < x ∧ x < 3
  println! "q          : {q}"
  println! "qe         : {← s.qe q}"
  println! "qeDisjunct : {← s.qeDisjunct q}"



/-! ## `smt!`

A binder's type is the variable's index, so the body is checked against it: a variable used at
the wrong sort, or a body that is not a formula, does not compile.
-/

/-- info:
forall : (forall ((x Int) (y Int)) (= (+ x y) (+ y x)))
mixed  : (exists ((x Int) (b Bool)) (and b (> x z)))
nested : (forall ((x Int)) (exists ((y Int)) (> y x)))
inside : (and p (forall ((x Int)) (= x x)))
-/
#guard_msgs in #eval Env.runIO do
  let z ← Term.mkSymbolAs Int "z"
  let p ← Term.mkSymbolAs Bool "p"
  println! "forall : {← smt! ∀ (x y : Int), x + y = y + x}"
  println! "mixed  : {← smt! ∃ (x : Int) (b : Bool), b ∧ x > z}"
  println! "nested : {← smt! ∀ (x : Int), ∃ (y : Int), y > x}"
  println! "inside : {← smt! p ∧ (∀ (x : Int), x = x)}"

/-- A quantified formula is a `Term Bool` whatever it binds. -/
example [Ω] : Env (Term Bool) := smt! ∀ (s : String) (r : Rat), s = s ∧ r = r

/--
error: Application type mismatch: The argument
  smtArg0✝
has type
  Term Int
but is expected to have type
  Term Bool
in the application
  smtArg0✝.and

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 6
-/
#guard_msgs in
example [Ω] : Env (Term Bool) := smt! ∀ (x : Int) (b : Bool), x ∧ b


/-! ## Signatures -/

section signatures
variable [Ω]

/-- info: @Term.mkForall : [inst : Ω] → (bvs : BVars) → Term Bool → autoParam (bvs ≠ []) Term.mkForall._auto_1 → Env (Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.mkForall

/-- info: @Term.forallH : [inst : Ω] → {φ : Type} → [Term.Binder φ] → φ → optParam (List String) [] → Env (Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.forallH

end signatures
