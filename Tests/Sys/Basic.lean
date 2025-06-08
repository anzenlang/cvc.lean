/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Tests.Basic



namespace Cvc.Test



open scoped Cvc.Term.Dsl
open scoped Cvc.State.Dsl
open scoped Cvc.Sys.Dsl


/-- State symbol-structure of the stopwatch system. -/
state structure Sw.State where
  /-- *Input*: start-stop button. -/
  startStop : Bool
  /-- *Input*: reset button. -/
  reset : Bool

  /-- *Internal*: start-stop input rising edge. -/
  risingStartStop : Bool
  /-- *Internal*: reset input rising edge. -/
  risingReset : Bool
  /-- *Internal*: flag indicating whether the system is currently counting. -/
  isCounting : Bool

  /-- *Output*: time counter. -/
  counter : Int

namespace Sw.Spec

def init : State.StatePred := smtPred! state =>
  ¬ state.risingStartStop ∧ ¬ state.risingReset ∧ ¬ state.isCounting ∧ state.counter = 0

def inputHandler : State.StateRel := smtRel! prev curr =>
  curr.risingStartStop = ¬ prev.startStop ∧ curr.startStop
  ∧
  curr.risingReset = ¬ prev.reset ∧ curr.reset

def isCountingStep : State.StateRel := smtRel! prev curr =>
  curr.isCounting =
    if curr.risingStartStop then ¬ prev.isCounting else prev.isCounting

def counterStep : State.StateRel := smtRel! prev curr =>
  curr.counter =
    if curr.risingReset then 0
    else if curr.isCounting then prev.counter + 1 else prev.counter

def step : State.StateRel := smtRel! prev curr =>
  ![inputHandler prev curr] ∧ ![counterStep prev curr] ∧ ![isCountingStep prev curr]

namespace candidates

def counterNot (n : Nat) : String × State.StatePred :=
  (s!"counter ≠ {n}", smtPred! state => state.counter ≠ ![Term.int n])

def counterNZ : String × State.StatePred :=
  counterNot 0

def isAlwaysCounting : String × State.StatePred :=
  ("isCounting", smtPred! state => state.isCounting)

def counterPos : String × State.StatePred :=
  ("0 ≤ counter", smtPred! state => 0 ≤ state.counter)

def neverReset : String × State.StatePred :=
  ("¬ reset", smtPred! state => ¬ state.reset)

def zeroOfReset : String × State.StatePred :=
  ("reset → counter = 0", smtPred! state => state.reset → state.counter = 0)

def zeroOfRisingReset : String × State.StatePred :=
  ("risingReset → counter = 0", smtPred! state => state.risingReset → state.counter = 0)

def counterNotMinusSeven : String × State.StatePred :=
  ("counter ≠ -7", smtPred! state => state.counter ≠ (-7))

end candidates

end Sw.Spec



/-- A simple stopwatch system. -/
system structure Sw for Sw.State where
  init : Sw.State.StatePred := Sw.Spec.init
  step : Sw.State.StateRel := Sw.Spec.step
  namedCandidates := .empty

namespace Sw

def mkWith (candidates : List (String × Sw.StatePred)) : Res Sw :=
  mk.addCandidates candidates

def printLines (sw : Sw k) (desc : String := "sw") : IO Unit := do
  println! "\n{desc}, depth is {sw.depth}:"
  for line in sw.toLines "  " do
    println! line

def printState (state : Sw.instState.ValsAt k) (pref := "") : IO Unit := do
  println! "{pref}inputs    | \
    startStop: {state.startStop}, reset: {state.reset}\
  "
  println! "{pref}internals | \
    risingReset: {state.risingReset}, risingStartStop: {state.risingStartStop}, \
    isCounting: {state.isCounting}\
  "
  println! "{pref}output    | counter: {state.counter}"

def printTrace (trace : Sw.instState.ValTrace k) (pref := "") : IO Unit := do
  for ⟨k, state⟩ in trace do
    println! "{pref}- at {k}"
    printState state (pref ++ "  ")

def printCexs {k : Nat} (sw : Sw k.succ) (pref := "") : IO Unit := do
  let fls := sw.candidates.falsified
  println! "{fls.size} falsified candidate(s)"
  for (name, fls) in fls do
    println! "- `{name}`"
    printTrace fls.data.cex (pref ++ "  ")


end Sw


Smt.test! [Sys.basics.manualCex0]
  Smt.setOption Cvc.Option.produceModels
  -- let sw ← Sw.mkWith [Sw.Spec.candidates.counterPos, Sw.Spec.candidates.zeroOfReset]
  let sw ← Sw.mkWith [Sw.Spec.candidates.counterNZ]
  -- sw.printLines "initial sw"
  if h : ¬ sw.isDone then
    -- println! "\nunrolling..."
    let sw ← sw.unroll
    -- Sw.printLines sw
    if h : ¬ sw.isBaseOver then
      let sw ← sw.checkBase
      Sw.printLines sw "base-checked sw"
      if ¬ sw.candidates.unknown.isEmpty ∨ ¬ sw.candidates.invariant.isEmpty then
        println! "expected empty unknown/invariant candidates"
      Sw.printCexs sw
/-- info:
base-checked sw, depth is 1:
  candidates at 0 {
    no unknown
    no invariant
    falsified: {}
      `counter ≠ 0`: falsified at 0
    }
  }
1 falsified candidate(s)
- `counter ≠ 0`
  - at 0
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
-/

Smt.test! [Sys.basics.kInductionCex0]
  Smt.setOption Cvc.Option.produceModels
  let sw ← Sw.mkWith [Sw.Spec.candidates.counterNZ]
  -- sw.printLines "initial sw"
  let ⟨k, sw⟩ ← sw.kInduction 1
  println! "k-induction stopped at `{k}`"
  Sw.printLines sw
  match k with
  | 0 => println! "cannot be stopped at 0"
  | _+1 => Sw.printCexs sw
/-- info:
k-induction stopped at `1`

sw, depth is 1:
  candidates at 0 {
    no unknown
    no invariant
    falsified: {}
      `counter ≠ 0`: falsified at 0
    }
  }
1 falsified candidate(s)
- `counter ≠ 0`
  - at 0
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
-/

Smt.test! [Sys.basics.kInductionCex5]
  Smt.setOption Cvc.Option.produceModels
  let sw ← Sw.mkWith [Sw.Spec.candidates.counterNot 5]
  sw.printLines "initial sw"
  let ⟨k, sw⟩ ← sw.kInduction 10
  println! "k-induction stopped at `{k}`"
  Sw.printLines sw "base-checked sw"
  match k with
  | 0 => println! "cannot be stopped at 0"
  | _+1 => Sw.printCexs sw
/-- info:
initial sw, depth is 0:
  candidates in init {
    unknown: {}
      `counter ≠ 5`: init
    }
  }
k-induction stopped at `6`

base-checked sw, depth is 6:
  candidates at 5 {
    no unknown
    no invariant
    falsified: {}
      `counter ≠ 5`: falsified at 5
    }
  }
1 falsified candidate(s)
- `counter ≠ 5`
  - at 5
    inputs    | startStop: true, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 5
  - at 4
    inputs    | startStop: true, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 4
  - at 3
    inputs    | startStop: true, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 3
  - at 2
    inputs    | startStop: true, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 2
  - at 1
    inputs    | startStop: true, reset: true
    internals | risingReset: false, risingStartStop: true, isCounting: true
    output    | counter: 1
  - at 0
    inputs    | startStop: false, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
-/

Smt.test! [Sys.basics.kInduction1]
  Smt.setOption Cvc.Option.produceModels
  let sw ← Sw.mkWith [Sw.Spec.candidates.counterPos, Sw.Spec.candidates.zeroOfReset]
  let steps := 2
  println! "\nrunning k-induction, step(s) := {steps}"
  let ⟨k, sw⟩ ← sw.kInduction steps
  println! "k-induction stopped at {k}"
  println! "sw@{sw.depth}:"
  for line in sw.toLines "  " do
    println! line
  match k with
  | 0 => println! "cannot be stopped at 0"
  | _+1 => Sw.printCexs sw
/-- info:
running k-induction, step(s) := 2
k-induction stopped at 2
sw@2:
  candidates at 1 {
    no unknown
    invariant: {}
      `0 ≤ counter`: 1-inductive
    }
    falsified: {}
      `reset → counter = 0`: falsified at 1
    }
  }
1 falsified candidate(s)
- `reset → counter = 0`
  - at 1
    inputs    | startStop: true, reset: true
    internals | risingReset: false, risingStartStop: true, isCounting: true
    output    | counter: 1
  - at 0
    inputs    | startStop: false, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
-/

Smt.test! [Sys.basics.kInduction2]
  Smt.setOption Cvc.Option.produceModels
  let sw ← Sw.mkWith [Sw.Spec.candidates.counterNotMinusSeven]
  let steps := 5
  println! "\nrunning k-induction, step(s) := {steps}"
  let ⟨k, sw⟩ ← sw.kInduction steps
  println! "k-induction stopped at {k}"
  println! "sw@{sw.depth}:"
  for line in sw.toLines "  " do
    println! line
  match k with
  | 0 => println! "cannot be stopped at 0"
  | _+1 => Sw.printCexs sw
/-- info:
running k-induction, step(s) := 5
k-induction stopped at 5
sw@5:
  candidates at 4 {
    unknown: {}
      `counter ≠ -7`: baseValidUpTo: (some 4), stepInvalidUpTo: (some 4), stepValidAt: none, [isPrevBaseValid/isBaseValid]: false/true, [isPrevStepInvalid/isStepInvalid]: false/true
    }
    no invariant
    no falsified
  }
0 falsified candidate(s)
-/

Smt.test! [Sys.basics.kInduction3]
  Smt.setOption Cvc.Option.produceModels
  let sw ← Sw.mkWith [
    Sw.Spec.candidates.counterPos,
    Sw.Spec.candidates.zeroOfRisingReset,
    Sw.Spec.candidates.counterNotMinusSeven
  ]
  let steps := 5
  println! "\nrunning k-induction, step(s) := {steps}"
  let ⟨k, sw⟩ ← sw.kInduction steps
  println! "k-induction stopped at {k}"
  println! "sw@{sw.depth}:"
  for line in sw.toLines "  " do
    println! line
  match k with
  | 0 => println! "cannot be stopped at 0"
  | _+1 => Sw.printCexs sw
/-- info:
running k-induction, step(s) := 5
k-induction stopped at 2
sw@2:
  candidates at 1 {
    no unknown
    invariant: {}
      `0 ≤ counter`: 1-inductive
      `counter ≠ -7`: 1-inductive
      `risingReset → counter = 0`: 1-inductive
    }
    no falsified
  }
0 falsified candidate(s)
-/
