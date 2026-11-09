/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Extra.Sys
import Cvc.Typed.Theory.Arith

meta import Cvc.Typed.Extra.Sys
meta import Cvc.Typed.Theory.Arith



/-! # Transition systems, typed

`Sys.Bmc` is exercised by the worked example `CvcExamples.Typed.Bmc`. What is checked here is what
a hand-written unrolling uses: the system's predicates at given steps, and reading a run back out of
a model, each symbol at its own index.
-/
namespace Cvc.Tests.Typed.Sys

open Cvc Typed

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

`initAt` and `nextAt` answer formulas over the steps' symbols; a model of the unrolling reads back
as Lean values (`getCex`) or as terms at each symbol's index (`getTermCex`), from step `0` up.
-/

/-- info:
init     : (= count__@__0 0)
next     : (= count__@__1 (ite up__@__1 (+ count__@__0 1) (- count__@__0 1)))
@0 : up false, count 0
@1 : up false, count -1
@2 : up true, count 0
@3 : up true, count 1
terms @3 : up true, count 1
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let init : Term Bool ← counter.initAt s 0
  println! "init     : {init}"
  s.assert init
  let s0 ← s.declareSymbolsAt 0 counter.idents
  let s1 ← s.declareSymbolsAt 1 counter.idents
  let next : Term Bool ← counter.nextAt s0 s1
  println! "next     : {next}"
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
    cex.iterM fun {k} values => do
      let count : Int := values.count.get
      println! "@{k} : up {values.up.get}, count {count}"
    let terms ← trace.getTermCex
    let count : Term Int := terms.getCurrent.count.get
    println! "terms @3 : up {terms.getCurrent.up.get}, count {count}")

/-! Where transition systems are imported, `structure.symbols` also aliases their traces. -/

/-- info: Cvc.Tests.Typed.Sys.Counter.TermTrace [Ω] (k : Nat) : Type -/
#guard_msgs in #check Counter.TermTrace
