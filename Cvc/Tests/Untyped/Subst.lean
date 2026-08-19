/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core
import Cvc.Untyped.Theory.Arith
import Cvc.Untyped.Solver

meta import Cvc.Untyped.Core
meta import Cvc.Untyped.Theory.Arith
meta import Cvc.Untyped.Solver



/-! # Substitution, sort-erased

cvc5 substitutes **simultaneously and once**: sources are matched in a single pre-order pass, so a
replacement is never itself rewritten and the result is not driven to a fixed point.
-/
namespace Cvc.Tests.Untyped.Subst

open Cvc
open Cvc.Untyped

/-- Four integer constants and the term `x + y`. -/
def setup [Ω] : Env (Term × Term × Term × Term × Term) := do
  let s ← Solver.new
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  let z ← s.declareConst "z" int
  let w ← s.declareConst "w" int
  return (x, y, z, w, ← Term.add x y)



/-! ## What substitution does -/

/-- info:
base         : (+ x y)
x ↦ z        : (+ z y)
absent       : (+ x y)
whole term   : w
-/
#guard_msgs in #eval Env.runIO do
  let (x, _y, z, w, sum) ← setup
  println! "base         : {sum}"
  println! "x ↦ z        : {← sum.substitute #[(x, z)]}"
  -- a source that does not occur changes nothing
  println! "absent       : {← sum.substitute #[(w, z)]}"
  -- a source need not be a variable: any sub-term will do, including the whole term
  println! "whole term   : {← sum.substitute #[(sum, w)]}"

/-! The three semantics worth pinning, each of which a naive implementation would get wrong. -/

/-- info:
simultaneous : (+ y x)
once only    : (+ (* z z) y)
dup earliest : (+ z y)
-/
#guard_msgs in #eval Env.runIO do
  let (x, y, z, w, sum) ← setup
  -- simultaneous, so `x ↦ y` and `y ↦ x` swap rather than compose into `y ↦ y`
  println! "simultaneous : {← sum.substitute #[(x, y), (y, x)]}"
  -- applied once: the `z` introduced by the first pair is *not* then rewritten by the second
  println! "once only    : {← sum.substitute #[(x, ← Term.mul z z), (z, w)]}"
  -- where a source is repeated, the earliest pair wins
  println! "dup earliest : {← sum.substitute #[(x, z), (x, w)]}"



/-! ## The parallel-array form

`substitute'` is what cvc5 takes. Its side condition is the 1:1 mapping cvc5 requires, discharged
at elaboration rather than left to fail at run time.
-/

/-- info: parallel : (+ z w) -/
#guard_msgs in #eval Env.runIO do
  let (x, y, z, w, sum) ← setup
  println! "parallel : {← sum.substitute' #[x, y] #[z, w]}"

/-- error: could not synthesize default value for parameter 'valid' using tactics
---
error: failed to prove there are as many replacements as sub-terms
inst✝ : Ω
t x : Term
⊢ #[x].size = #[].size
-/
#guard_msgs in
example [Ω] (t x : Term) : Env Term := t.substitute' #[x] #[]
