/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Quant
import Cvc.Untyped.Theory.Arith
import Cvc.Untyped.Core.Solver

meta import Cvc.Untyped.Theory.Quant
meta import Cvc.Untyped.Theory.Arith
meta import Cvc.Untyped.Core.Solver



/-! # Quantifiers, sort-erased

Both spellings are checked to build the same formula, then quantified formulas are solved over, and
finally quantifier elimination is run on them — which is what the constructors unblock.
-/
namespace Cvc.Tests.Untyped.Term.Quant

open Cvc
open Cvc.Untyped

/-! ## Construction -/

/-- info:
forall  : (forall ((x Int) (y Int)) (= (+ x y) (+ y x)))
exists  : (exists ((x Int)) (> x y))
forallH : (forall ((x Int) (y Int)) (= (+ x y) (+ y x)))
existsH : (exists ((x Int)) (> x y))
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let y ← Term.mkSymbol int "y"

  let x ← BVar.mk int "x"
  let x' ← BVar.mk int "y"
  let comm ← Term.equal (← Term.add x x') (← Term.add x' x)
  println! "forall  : {← Term.mkForall #[x, x'] comm}"
  println! "exists  : {← Term.mkExists #[x] (← Term.gt x y)}"

  let comm ← Term.forallH [("x", int), ("y", int)] fun x y => do
    Term.equal (← Term.add x y) (← Term.add y x)
  println! "forallH : {comm}"
  println! "existsH : {← Term.existsH [("x", int)] fun x => Term.gt x y}"

/-! The number of binders is a runtime fact sort-erased, checked against the body's arity. -/

/-- info:
too few  : the body binds 2 variables, but 1 binder was given
too many : the body binds 1 variable, but 2 binders were given
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let report (code : Env Term) : Env String := do
    try discard code; return "no error" catch e => return e.toString
  let few ← report <| Term.forallH [("x", int)] fun x y => Term.equal x y
  let many ← report <| Term.forallH [("x", int), ("y", int)] fun x => Term.equal x x
  println! "too few  : {few}"
  println! "too many : {many}"

/--
error: could not synthesize default value for parameter '_nonEmpty' using tactics
---
error: failed to prove a quantifier binds at least one variable
inst✝ : Ω
body : Term
⊢ 0 < #[].size
-/
#guard_msgs in
example [Ω] (body : Term) : Env Term := Term.mkForall #[] body



/-! ## Solving -/

/-- info:
∀ x, x + y = y + x : sat
∀ x, x > y         : unsat
∃ x, x > y         : sat
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let check (name : String) (f : Solver → Term → Env Term) : Env Unit := do
    let s ← Solver.new
    let y ← s.declareConst "y" int
    s.assert (← f s y)
    println! "{name} : {if ← s.checkIsSat then "sat" else "unsat"}"
  check "∀ x, x + y = y + x" fun _ y =>
    Term.forallH [("x", int)] fun x => do Term.equal (← Term.add x y) (← Term.add y x)
  check "∀ x, x > y        " fun _ y => Term.forallH [("x", int)] fun x => Term.gt x y
  check "∃ x, x > y        " fun _ y => Term.existsH [("x", int)] fun x => Term.gt x y



/-! ## Quantifier elimination

`∃ x, y < x ∧ x < 3` over the integers holds exactly when `y < 2`, which is what `qe` should
eliminate it to. `qeDisjunct` answers one disjunct at a time; on a formula this small the first is
the whole answer.
-/

/-- info:
qe         : (not (>= y 2))
qeDisjunct : (some (not (>= y 2)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let int ← Srt.int
  let y ← s.declareConst "y" int
  let three ← Term.mkInt 3
  let q ← Term.existsH [("x", int)] fun x => do
    Term.and (← Term.lt y x) (← Term.lt x three)
  println! "qe         : {← s.qe q}"
  println! "qeDisjunct : {← s.qeDisjunct q}"



/-! ## `smt!`

A binder's sort is a Lean type or a `Srt`, freely mixed. Each variable is named as written, a nested
quantifier sees the outer one's variables, and in argument position a quantifier is parenthesized.
-/

/-- info:
forall : (forall ((x Int) (y Int)) (= (+ x y) (+ y x)))
mixed  : (exists ((x Int) (b Bool)) (and b (> x z)))
nested : (forall ((x Int)) (exists ((y Int)) (> y x)))
inside : (and p (forall ((x Int)) (= x x)))
types  : (exists ((x Int) (b Bool)) (and b (> x z)))
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let z ← Term.mkSymbol int "z"
  let p ← Term.mkSymbol bool "p"
  println! "forall : {← smt! ∀ (x y : int), x + y = y + x}"
  println! "mixed  : {← smt! ∃ (x : int) (b : bool), b ∧ x > z}"
  println! "nested : {← smt! ∀ (x : int), ∃ (y : int), y > x}"
  println! "inside : {← smt! p ∧ (∀ (x : int), x = x)}"
  println! "types  : {← smt! ∃ (x : Int) (b : bool), b ∧ x > z}"

/-! A sort is a Lean type or a `Srt`, and nothing else. -/

/--
error: expected a Lean type or a `Srt`, but `n` has type
  Nat
-/
#guard_msgs in
example [Ω] (n : Nat) : Env Term := smt! ∀ (x : n), x = x
