/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Defs
import Tests.Basic



namespace Cvc.Test


open scoped Cvc.Term.Dsl
open scoped Cvc.Sys.Dsl



abbrev Sw.State Data := ESymbols.ByName Data

namespace Sw.State

export ESymbols.ByName (StatePred StateRel)

def idents : ESymbols.ByName.Idents :=
  ESymbols.ByName.emptyIdents
  |>.insert! "startStop" Bool
  |>.insert! "reset" Bool
  |>.insert! "risingStartStop" Bool
  |>.insert! "risingReset" Bool
  |>.insert! "isCounting" Bool
  |>.insert! "counter" Int

variable (state : State R)

def unwrap [ToString α] : Res α → String
| .ok a => toString a
| .error e => s!"{e}"

def startStop [S : ToString (R Bool)] (state : State R) :=
  state.findAs Bool "startStop" |> @unwrap (R Bool) S
def reset [S : ToString (R Bool)] (state : State R) :=
  state.findAs Bool "reset" |> @unwrap (R Bool) S
def risingStartStop [S : ToString (R Bool)] (state : State R) :=
  state.findAs Bool "risingStartStop" |> @unwrap (R Bool) S
def risingReset [S : ToString (R Bool)] (state : State R) :=
  state.findAs Bool "risingReset" |> @unwrap (R Bool) S
def isCounting [S : ToString (R Bool)] (state : State R) :=
  state.findAs Bool "isCounting" |> @unwrap (R Bool) S
def counter [S : ToString (R Int)] (state : State R) :=
  state.findAs Int "counter" |> @unwrap (R Int) S

end Sw.State



system structure Sw for Sw.State where
  init : Sw.State.StatePred := smtPred! state =>
    ¬ ![state.findAs Bool "risingStartStop"]
    ∧ ¬ ![state.findAs Bool "risingReset"]
    ∧ ¬ ![state.findAs Bool "isCounting"]
    ∧ ![state.findAs Int "counter"] = 0
  step : Sw.State.StateRel := smtRel! prev curr =>
    (
      ![curr.findAs Bool "risingStartStop"] =
        (![curr.findAs Bool "startStop"] ∧ ¬ ![prev.findAs Bool "startStop"])
    ) ∧ (
      ![curr.findAs Bool "risingReset"] =
        (![curr.findAs Bool "reset"] ∧ ¬ ![prev.findAs Bool "reset"])
    ) ∧ (
      ![curr.findAs Bool "isCounting"] =
        if ![curr.findAs Bool "risingStartStop"]
        then ¬ ![prev.findAs Bool "isCounting"]
        else ![prev.findAs Bool "isCounting"]
    ) ∧ (
      ![curr.findAs Int "counter"] =
        if ![curr.findAs Bool "risingReset"] then 0
        else ![prev.findAs Int "counter"] + (
          if ![curr.findAs Bool "isCounting"] then 1 else 0
        )
    )
  namedCandidates := .ofList [
    ("counter ≠ 0", smtPred! state => ![state.findAs Int "counter"] ≠ 0),
    ("counter ≠ 5", smtPred! state => ![state.findAs Int "counter"] ≠ 5),
    ("always counting", smtPred! state => ![state.findAs Bool "isCounting"]),
    ("0 ≤ counter", smtPred! state => 0 ≤ ![state.findAs Int "counter"]),
    ("¬ reset", smtPred! state => ¬ ![state.findAs Bool "reset"]),
    ("reset → counter = 0", smtPred!
      state => ![state.findAs Bool "reset"] → ![state.findAs Int "counter"] = 0
    ),
    ("risingReset → counter = 0", smtPred!
      state => ![state.findAs Bool "risingReset"] → ![state.findAs Int "counter"] = 0
    ),
    ("counter ≠ -7", smtPred! state => ![state.findAs Int "counter"] = (-7)),
  ]

namespace Sw

def mk := Sw.ofIdents Sw.State.idents

def printLines (sw : Sw k) (desc : String := "sw") : IO Unit := do
  println! "\n{desc}, depth is {sw.depth}:"
  for line in sw.toLines "  " do
    println! line

def printState (state : Sw.instState.ValuesAt k) (pref := "") : IO Unit := do
  println! "{pref}inputs    | \
    startStop: {state.startStop}, reset: {state.reset}\
  "
  println! "{pref}internals | \
    risingReset: {state.risingReset}, risingStartStop: {state.risingStartStop}, \
    isCounting: {state.isCounting}\
  "
  println! "{pref}output    | counter: {state.counter}"

def printTrace (trace : Sw.instState.ValueTrace k) (pref := "") : IO Unit := do
  for ⟨k, state⟩ in trace do
    println! "{pref}- at {k}"
    printState state (pref ++ "  ")

def printCexs : {k : Nat} → (sw : Sw k) → (pref : String := "") → IO Unit
| 0, _, _ => println! "error: cannot print cex-s on a system at `k = 0`"
| _ + 1, sw, pref => do
  let fls := sw.candidates.falsified
  println! "{fls.size} falsified candidate(s)"
  for (name, fls) in fls do
    println! "- `{name}`"
    printTrace fls.data.cex (pref ++ "  ")

end Sw


Smt.test! [ESys.sw.all]
  Smt.setOption Cvc.Option.produceModels
  let sw := Sw.mk
  let steps := 10
  println! "\nrunning k-induction, step(s) := {steps}"
  let ⟨k, sw⟩ ← sw.kInduction steps
  println! "k-induction stopped at {k}"
  println! "sw@{sw.depth}:"
  for line in sw.toLines "  " do
    println! line
  Sw.printCexs sw
/-- info:
running k-induction, step(s) := 10
k-induction stopped at 6
sw@6:
  candidates at 5 {
    no unknown
    invariant: {}
      `0 ≤ counter`: 1-inductive
      `risingReset → counter = 0`: 1-inductive
    }
    falsified: {}
      `always counting`: falsified at 0
      `counter ≠ -7`: falsified at 0
      `counter ≠ 0`: falsified at 0
      `counter ≠ 5`: falsified at 5
      `reset → counter = 0`: falsified at 1
      `¬ reset`: falsified at 0
    }
  }
6 falsified candidate(s)
- `always counting`
  - at 0
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
- `counter ≠ -7`
  - at 0
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
- `counter ≠ 0`
  - at 0
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
- `counter ≠ 5`
  - at 5
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 5
  - at 4
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 4
  - at 3
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 3
  - at 2
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: true
    output    | counter: 2
  - at 1
    inputs    | startStop: true, reset: false
    internals | risingReset: false, risingStartStop: true, isCounting: true
    output    | counter: 1
  - at 0
    inputs    | startStop: false, reset: false
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
- `reset → counter = 0`
  - at 1
    inputs    | startStop: true, reset: true
    internals | risingReset: false, risingStartStop: true, isCounting: true
    output    | counter: 1
  - at 0
    inputs    | startStop: false, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
- `¬ reset`
  - at 0
    inputs    | startStop: false, reset: true
    internals | risingReset: false, risingStartStop: false, isCounting: false
    output    | counter: 0
-/
