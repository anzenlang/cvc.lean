/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Fun
import Cvc.Typed.Theory.Arith
import Cvc.Typed.Solver

public meta import Cvc.Typed.Theory.Fun
public meta import Cvc.Typed.Theory.Arith
public meta import Cvc.Typed.Solver



/-! # Generated function-application constructors, typed

Construction is checked against the SMT-LIB cvc5 prints, and then end to end: an uninterpreted
function is declared, constrained, and its value read back out of a model. Getting the sort wrong
would be caught by the solver rather than by the term builder, so both halves matter.
-/
namespace Cvc.Tests.Typed.Term.Fun

open Cvc
open Cvc.Typed.Term

/-- info:
apply           : (f i)
apply2          : (g i b)
apply3          : (h i b r)
applyHo         : (@ f i)
applyHo partial : (@ g i)
applyHo chained : (@ (@ g i) b)
higher-order    : (hof f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Typed.Term.mkSymbolAs (Int → Bool) "f"
  let g ← Cvc.Typed.Term.mkSymbolAs (Int → Bool → Rat) "g"
  let h ← Cvc.Typed.Term.mkSymbolAs (Int → Bool → Rat → Int) "h"
  let hof ← Cvc.Typed.Term.mkSymbolAs ((Int → Bool) → Rat) "hof"
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let b ← Cvc.Typed.Term.mkSymbolAs Bool "b"
  let r ← Cvc.Typed.Term.mkSymbolAs Rat "r"

  println! "apply           : {← apply f i}"
  println! "apply2          : {← apply2 g i b}"
  println! "apply3          : {← apply3 h i b r}"
  println! "applyHo         : {← applyHo f i}"
  println! "applyHo partial : {← applyHo g i}"
  println! "applyHo chained : {← applyHo (← applyHo g i) b}"
  println! "higher-order    : {← apply hof f}"



/-! ## End to end -/

/-- info: f(1) = 2 -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Typed.Solver.new
  solver.setOption "produce-models" "true"

  let f ← Cvc.Typed.Term.mkSymbolAs (Int → Int) "f"
  let one ← Cvc.Typed.Term.mkInt 1
  let two ← Cvc.Typed.Term.mkInt 2
  let three ← Cvc.Typed.Term.mkInt 3

  let fOne ← apply f one
  let fTwo ← apply f two
  equal fOne two >>= solver.assert
  equal fTwo three >>= solver.assert

  let value ← solver.checkSat (ifSat := solver.getValue fOne)
  println! "f(1) = {value}"

/-- info: g(1, 2) = 5 -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Typed.Solver.new
  solver.setOption "produce-models" "true"

  let g ← Cvc.Typed.Term.mkSymbolAs (Int → Int → Int) "g"
  let one ← Cvc.Typed.Term.mkInt 1
  let two ← Cvc.Typed.Term.mkInt 2
  let five ← Cvc.Typed.Term.mkInt 5

  let g12 ← apply2 g one two
  equal g12 five >>= solver.assert

  let value ← solver.checkSat (ifSat := solver.getValue g12)
  println! "g(1, 2) = {value}"

-- a function is a function: the same argument cannot map to two values
/-- info: f(x) = 1 ∧ f(x) = 2 → unsat -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Typed.Solver.new

  let f ← Cvc.Typed.Term.mkSymbolAs (Int → Int) "f"
  let x ← Cvc.Typed.Term.mkSymbolAs Int "x"
  let one ← Cvc.Typed.Term.mkInt 1
  let two ← Cvc.Typed.Term.mkInt 2

  let fx ← apply f x
  equal fx one >>= solver.assert
  equal fx two >>= solver.assert

  let result ← solver.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
  println! "f(x) = 1 ∧ f(x) = 2 → {result}"

-- congruence: equal arguments give equal results, so this is unsat
/-- info: x = y ∧ f(x) ≠ f(y) → unsat -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Typed.Solver.new

  let f ← Cvc.Typed.Term.mkSymbolAs (Int → Int) "f"
  let x ← Cvc.Typed.Term.mkSymbolAs Int "x"
  let y ← Cvc.Typed.Term.mkSymbolAs Int "y"

  equal x y >>= solver.assert
  (do distinct (← apply f x) (← apply f y)) >>= solver.assert

  let result ← solver.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
  println! "x = y ∧ f(x) ≠ f(y) → {result}"



/-! ## Applying any number of arguments

`applyN` takes an `Args` spine, so the arity is not capped at the three fixed spellings. Stopping
the spine early is a partial application, and the index the spine computes is the sort cvc5 gives.
-/

/-- info:
apply2   : (f i b) : Int
applyN 2 : (f i b) : Int
applyN 4 : (g i i i i) : Int
partial  : (f i) : (-> Bool Int)
lambda   : (@ (@ (lambda ((x Int) (y Int)) (+ x y)) i) i) : Int
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Typed.Solver.new
  let f ← s.declareFun (α := Int → Bool → Int) "f"
  let g ← s.declareFun (α := Int → Int → Int → Int → Int) "g"
  let i ← s.declareConst Int "i"
  let b ← s.declareConst Bool "b"

  let show! (label : String) (t : Untyped.Term) : Env Unit := do
    println! "{label} : {t} : {← t.getSort}"

  -- the fixed-arity spelling and the spine agree
  show! "apply2  " (← apply2 f i b).erase
  show! "applyN 2" (← applyN f (.cons i (.last b))).erase
  -- past three arguments only the spine will do
  show! "applyN 4" (← applyN g (.cons i (.cons i (.cons i (.last i))))).erase
  -- stopping early leaves the rest of the arrow
  show! "partial " (← applyN f (.last i)).erase

  -- and it applies a lambda, whose index the binders determine
  let x ← Cvc.Typed.BVar.mk (α := Int) "x"
  let y ← Cvc.Typed.BVar.mk (α := Int) "y"
  let lam ← Cvc.Typed.BVars.lambda
    (Cvc.Typed.BVars.push y (Cvc.Typed.BVars.push x []))
    (← add x.toTerm y.toTerm)
  show! "lambda  " (← applyN lam (.cons i (.last i))).erase

section indices
variable [Ω]
  (f : Cvc.Typed.Term (Int → Bool → Rat → Int))
  (i : Cvc.Typed.Term Int) (b : Cvc.Typed.Term Bool)
  (r : Cvc.Typed.Term Rat)

/-- Saturating gives the codomain. -/
example : Env (Cvc.Typed.Term Int) := applyN f (.cons i (.cons b (.last r)))
/-- One argument leaves the other two. -/
example : Env (Cvc.Typed.Term (Bool → Rat → Int)) := applyN f (.last i)
/-- Two leave one. -/
example : Env (Cvc.Typed.Term (Rat → Int)) := applyN f (.cons i (.last b))

-- an argument of the wrong index is rejected
#guard_msgs(drop error) in example := applyN f (.last b)
-- a spine with nothing in it cannot even be written: `Args.last` carries an argument, so
-- "at least one" is structural rather than a side condition

end indices



/-! ## Flattening

Applying a term that is already an `APPLY_UF` appends to its children rather than nesting, which
the typed constructors inherit from the sort-erased ones. So every spelling of the same application
— including the `CoeFun` chain — builds one flat term, and none of them creates the function-sorted
intermediate that would force a higher-order logic.
-/

/-- info:
applyN     : (f i b r)
apply3     : (f i b r)
coe chain  : (f i b r)
apply then : (f i b r)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Typed.Solver.new
  let f ← s.declareFun (α := Int → Bool → Rat → Int) "f"
  let i ← s.declareConst Int "i"
  let b ← s.declareConst Bool "b"
  let r ← s.declareConst Rat "r"

  println! "applyN     : {(← applyN f (.cons i (.cons b (.last r)))).erase}"
  println! "apply3     : {(← apply3 f i b r).erase}"
  -- `f i b r` goes through the two `CoeFun` instances
  println! "coe chain  : {(← (f i b r : Env (Cvc.Typed.Term Int))).erase}"
  -- and reaching it in two steps is the same term again
  println! "apply then : {(← apply2 (← apply f i) b r).erase}"

/-- info: coe chain, no logic set : sat -/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Typed.Solver.new
  let f ← s.declareFun (α := Int → Bool → Int) "f"
  let i ← s.declareConst Int "i"
  let b ← s.declareConst Bool "b"
  let applied ← f i b
  (do equal applied (← mkInt 1)) >>= s.assert
  println! "coe chain, no logic set : {if ← s.checkIsSat then "sat" else "unsat"}"
