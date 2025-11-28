/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Defs
import Cvc.Ext



namespace Cvc.Tests

/-- info:
- bool := Bool
- int := Int
- array := (Array Bool Int)
- bag := (Bag (Array Bool Int))
-/
#guard_msgs in #eval Env.runIO do
  let bool ← Srt.bool
  println! "- bool := {←bool.toSmtString}"
  let int ← Srt.int
  println! "- int := {←int.toSmtString}"
  let array ← Srt.array bool int
  println! "- array := {←array.toSmtString}"
  let bag ← Srt.bag array
  println! "- bag := {←bag.toSmtString}"

/-- info:
- term1 := false
- term2 := (not false)
-/
#guard_msgs in #eval Env.runIO do
  let term1 ← Term.bool false
  println! "- term1 := {←term1.toSmtString}"
  let term2 ← term1.not
  println! "- term2 := {←term2.toSmtString}"

/-- info:
- a : Bool := a
- res := sat
-/
#guard_msgs in #eval Env.runIO do
  let solver ← Solver.mk
  let bool ← Srt.bool
  let a ← solver.declareConst "a" bool
  println! "- a : {←bool.toSmtString} := {←a.toSmtString}"
  solver.assert a
  let res ← solver.checkSat?
  println! "- res := {res}"

/-- info:
- asserting (ite b1 (not (xor b2 b3)) (or b1 b2 b3))
- check-sat assuming b2
- res := sat
-/
#guard_msgs in open scoped Term.Dsl in #eval Env.runIO do
  let solver ← Solver.mk
  let bool ← Srt.bool
  let b1 ← solver.declareConst "b1" bool
  let b2 ← solver.declareConst "b2" bool
  let b3 ← solver.declareConst "b3" bool
  let prop ← smt!
    if b1 then ¬ (b2 ⊻ b3) else ∨[b1, b2, b3]
  println! "- asserting {← prop.toSmtString}"
  solver.assert prop
  println! "- check-sat assuming {← b2.toSmtString}"
  let res ← solver.checkSat? (assuming := #[b2])
  println! "- res := {res}"

/--
info: - asserting (ite (not b1) (not (xor b2 b3)) (or b1 b2 b3))
- check-sat assuming b2
- model
  - b1 ↦ true
  - b2 ↦ true
  - b3 ↦ false
  - irrelevant ↦ 0
-/
#guard_msgs in open scoped Term.Dsl in #eval Env.runIO do
  let solver ← Solver.mk
  solver.setOption "produce-models" "true"
  let bool ← Srt.bool
  let int ← Srt.int
  let b1 ← solver.declareConst "b1" bool
  let b2 ← solver.declareConst "b2" bool
  let b3 ← solver.declareConst "b3" bool
  let i ← solver.declareConst "irrelevant" int
  let prop ← smt!
    if ¬ b1 then ¬ (b2 ⊻ b3) else ∨[b1, b2, b3]
  println! "- asserting {← prop.toSmtString}"
  solver.assert prop
  println! "- check-sat assuming {← b2.toSmtString}"
  let model ← solver.checkSat (assuming := #[b2])
    (ifSat := solver.getValueMap #[b1, b2, b3, i])
  println! "- model"
  for (term, value) in model do
    println! "  - {← term.toSmtString} ↦ {← value.toSmtString}"




/-! ## Errors -/



/--
error: Application type mismatch: The argument
  bool
has type
  Srt
but is expected to have type
  ?m.9
in the application
  pure bool
-/
#guard_msgs in #eval do
  let srt ← Env.runIO do
    let bool ← Srt.bool
    return bool
  println! "does not compile"

/--
error: Application type mismatch: The argument
  tru
has type
  Term
but is expected to have type
  ?m.9
in the application
  pure tru
-/
#guard_msgs in #eval do
  let term ← Env.runIO do
    let tru ← Term.bool true
    return tru
  println! "does not compile"

/--
error: Application type mismatch: The argument
  s
has type
  Solver
but is expected to have type
  ?m.9
in the application
  pure s
-/
#guard_msgs in #eval do
  let solver ← Env.runIO do
    let s ← Solver.mk
    return s
  println! "does not compile"
