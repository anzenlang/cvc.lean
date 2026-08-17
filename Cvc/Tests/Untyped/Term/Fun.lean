/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Term.Fun
import Cvc.Untyped.Term.Arith
import Cvc.Untyped.Term.Bool
import Cvc.Untyped.Solver

public meta import Cvc.Untyped.Term.Fun
public meta import Cvc.Untyped.Term.Arith
public meta import Cvc.Untyped.Term.Bool
public meta import Cvc.Untyped.Solver



/-! # Generated function-application constructors, sort-erased

Construction is checked against the SMT-LIB cvc5 prints, and then end to end: an uninterpreted
function is declared, constrained, and its value read back out of a model. Getting the sort wrong
would be caught by the solver rather than by the term builder, so both halves matter.
-/
namespace Cvc.Tests.Untyped.Term.Fun

open Cvc
open Cvc.Untyped.Term

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
  let f ← Cvc.Untyped.Term.mkSymbolAs (Int → Bool) "f"
  let g ← Cvc.Untyped.Term.mkSymbolAs (Int → Bool → Rat) "g"
  let h ← Cvc.Untyped.Term.mkSymbolAs (Int → Bool → Rat → Int) "h"
  let hof ← Cvc.Untyped.Term.mkSymbolAs ((Int → Bool) → Rat) "hof"
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let b ← Cvc.Untyped.Term.mkSymbolAs Bool "b"
  let r ← Cvc.Untyped.Term.mkSymbolAs Rat "r"

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
  let solver ← Cvc.Untyped.Solver.new
  solver.setOption "produce-models" "true"

  let f ← Cvc.Untyped.Term.mkSymbolAs (Int → Int) "f"
  let one ← Cvc.Untyped.Term.mkInt 1
  let two ← Cvc.Untyped.Term.mkInt 2
  let three ← Cvc.Untyped.Term.mkInt 3

  let fOne ← apply f one
  let fTwo ← apply f two
  equal fOne two >>= solver.assert
  equal fTwo three >>= solver.assert

  let value ← solver.checkSat (ifSat := solver.getValue fOne)
  println! "f(1) = {value}"

/-- info: g(1, 2) = 5 -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Untyped.Solver.new
  solver.setOption "produce-models" "true"

  let g ← Cvc.Untyped.Term.mkSymbolAs (Int → Int → Int) "g"
  let one ← Cvc.Untyped.Term.mkInt 1
  let two ← Cvc.Untyped.Term.mkInt 2
  let five ← Cvc.Untyped.Term.mkInt 5

  let g12 ← apply2 g one two
  equal g12 five >>= solver.assert

  let value ← solver.checkSat (ifSat := solver.getValue g12)
  println! "g(1, 2) = {value}"

-- a function is a function: the same argument cannot map to two values
/-- info: f(x) = 1 ∧ f(x) = 2 → unsat -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Untyped.Solver.new

  let f ← Cvc.Untyped.Term.mkSymbolAs (Int → Int) "f"
  let x ← Cvc.Untyped.Term.mkSymbolAs Int "x"
  let one ← Cvc.Untyped.Term.mkInt 1
  let two ← Cvc.Untyped.Term.mkInt 2

  let fx ← apply f x
  equal fx one >>= solver.assert
  equal fx two >>= solver.assert

  let result ← solver.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
  println! "f(x) = 1 ∧ f(x) = 2 → {result}"

-- congruence: equal arguments give equal results, so this is unsat
/-- info: x = y ∧ f(x) ≠ f(y) → unsat -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Untyped.Solver.new

  let f ← Cvc.Untyped.Term.mkSymbolAs (Int → Int) "f"
  let x ← Cvc.Untyped.Term.mkSymbolAs Int "x"
  let y ← Cvc.Untyped.Term.mkSymbolAs Int "y"

  equal x y >>= solver.assert
  (do distinct (← apply f x) (← apply f y)) >>= solver.assert

  let result ← solver.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
  println! "x = y ∧ f(x) ≠ f(y) → {result}"



/-! ## Applying any number of arguments

`applyN` takes the arguments as an array, so the arity is not capped at the three fixed spellings.
It builds the same `APPLY_UF`, with the function as the first child.
-/

/-- info:
apply2 f i b : (f i b) : Int
applyN 2     : (f i b) : Int
applyN 4     : (g i i i i) : Int
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  let int ← Srt.int
  let f ← s.declareFun "f" #[int, ← Srt.bool] int
  let g ← s.declareFun "g" #[int, int, int, int] int
  let i ← s.declareConst "i" int
  let b ← s.declareConst "b" (← Srt.bool)

  let show! (label : String) (t : Cvc.Untyped.Term) : Env Unit := do
    println! "{label} : {t} : {← t.getSort}"

  -- the fixed-arity spelling and the array one agree
  show! "apply2 f i b" (← apply2 f i b)
  show! "applyN 2    " (← applyN f #[i, b])
  -- past three arguments only `applyN` will do
  show! "applyN 4    " (← applyN g #[i, i, i, i])

/-! A *partial* application is legal: cvc5 answers a term of the remaining function sort rather
than refusing. Too many arguments is an error, and so is none — though passing none is caught at
elaboration rather than by cvc5.
-/

/-- info:
partial 1 of 2 : (f i) : (-> Bool Int)
partial 2 of 4 : (g i i) : (-> Int Int Int)
too many       : [internal] too many arguments to operator
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  let int ← Srt.int
  let f ← s.declareFun "f" #[int, ← Srt.bool] int
  let g ← s.declareFun "g" #[int, int, int, int] int
  let i ← s.declareConst "i" int
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"

  println! "partial 1 of 2 : {(← applyN f #[i]) |> fun t => t} : {← (← applyN f #[i]).getSort}"
  println! "partial 2 of 4 : {(← applyN g #[i, i])} : {← (← applyN g #[i, i]).getSort}"
  println! "too many       : {← caught do pure s!"{← applyN f #[i, i, i]}"}"

-- no arguments at all is rejected before cvc5 sees it
/-- error: could not synthesize default value for parameter '_h' using tactics
---
error: failed to prove there is at least one argument
inst✝ : Ω
f : Untyped.Term
⊢ 0 < #[].size
-/
#guard_msgs in
example [Ω] (f : Cvc.Untyped.Term) : Env Cvc.Untyped.Term := applyN f #[]



/-! ## Flattening

Applying a term that is already an `APPLY_UF` appends to its children rather than nesting, so every
way of reaching the same application builds the same term. Without that, an intermediate like
`(f i)` would be *function-sorted*, and cvc5 admits those only under a higher-order logic.
-/

/-- info:
applyN #[i,i,i] : (f i i i)
apply3          : (f i i i)
apply then 2    : (f i i i)
apply x3        : (f i i i)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  let int ← Srt.int
  let f ← s.declareFun "f" #[int, int, int] int
  let i ← s.declareConst "i" int

  println! "applyN #[i,i,i] : {← applyN f #[i, i, i]}"
  println! "apply3          : {← apply3 f i i i}"
  -- reached in two steps, and in three
  println! "apply then 2    : {← apply2 (← apply f i) i i}"
  println! "apply x3        : {← apply (← apply (← apply f i) i) i}"

/-! The consequence: an application built stepwise still solves under the default logic, because no
function-sorted term is ever created.
-/

/-- info: stepwise, no logic set : sat -/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  let int ← Srt.int
  let f ← s.declareFun "f" #[int, int] int
  let i ← s.declareConst "i" int
  let applied ← apply (← apply f i) i
  (do equal applied (← mkInt 1)) >>= s.assert
  println! "stepwise, no logic set : {if ← s.checkIsSat then "sat" else "unsat"}"
