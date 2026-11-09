/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Extra.Sys
import Cvc.Untyped.Theory.Arith

meta import Cvc.Untyped.Extra.Sys
meta import Cvc.Untyped.Theory.Arith



/-! # Transition systems, sort-erased

`Sys.Bmc` is exercised by the worked example `CvcExamples.Untyped.Bmc`. What is checked here is
what a hand-written unrolling uses: the system's predicates at given steps, and reading a run back
out of a model, step by step.
-/
namespace Cvc.Tests.Untyped.Sys

open Cvc Untyped

variable [Ω]

/-- The state of a counter going up or down by one at each step. -/
structure.symbols Counter where
  up : Bool
  count : Int

/-- The counter, starting at zero, moving the way its next state's `up` says. -/
def counter : Sys Counter where
  idents := Counter.idents
  init state := smt! state.count = 0
  next state state' := smt! state'.count = if state'.up then state.count + 1 else state.count - 1
  candidates := #[]

/-! ## Unrolling by hand

`initAt` declares a step's symbols in the solver and answers the initial predicate over them;
declaring that step again, not fresh, answers the same symbols, which `nextAt` relates to the next
step's. A model of the unrolling, read back with `getCex` (Lean values) or `getTermCex` (terms), is
the run, from step `0` up.
-/

/-- info:
init       : (= count__@__0 0)
same terms : true
next       : (= count__@__1 (ite up__@__1 (+ count__@__0 1) (- count__@__0 1)))
@0 : up false, count 0
@1 : up false, count -1
@2 : up true, count 0
@3 : up true, count 1
current    : count 1, zero: count 0
terms @3   : up true, count 1
same as getValueTerms : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let init ← counter.initAt s 0
  println! "init       : {init}"
  s.assert init
  let s0 ← s.declareSymbolsAt 0 counter.idents
  let s0' ← s.declareSymbolsAt 0 counter.idents
  println! "same terms : {s0.count.get == s0'.count.get && s0.up.get == s0'.up.get}"
  let s1 ← s.declareSymbolsAt 1 counter.idents
  let next ← counter.nextAt s0 s1
  println! "next       : {next}"
  s.assert next
  let s2 ← s.declareSymbolsAt 2 counter.idents
  s.assert (← counter.nextAt s1 s2)
  let s3 ← s.declareSymbolsAt 3 counter.idents
  s.assert (← counter.nextAt s2 s3)
  -- going down into step 1 and reaching 1 at step 3 forces going up into steps 2 and 3
  s.assert (← smt! ¬ s0.up ∧ ¬ s1.up ∧ s3.count = 1)
  let trace : Counter.TermTrace 3 := .cons s3 (.cons s2 (.cons s1 (.zero s0)))
  s.checkSat (ifSat := do
    let cex ← trace.getCex
    cex.iterM fun {k} values =>
      println! "@{k} : up {values.up.get}, count {values.count.get}"
    println! "current    : count {cex.getCurrent.count.get}, zero: count {cex.getZero.count.get}"
    let terms ← trace.getTermCex
    println! "terms @3   : up {terms.getCurrent.up.get}, count {terms.getCurrent.count.get}"
    let terms' ← trace.getValueTerms
    println! "same as getValueTerms : {terms.getCurrent.count.get == terms'.getCurrent.count.get}")

/-! Where transition systems are imported, `structure.symbols` also aliases their traces. -/

/-- info: Cvc.Tests.Untyped.Sys.Counter.TermTrace [Ω] (k : Nat) : Type -/
#guard_msgs in #check Counter.TermTrace
