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

export ESymbols.ByName (StatePred StateRel getAs)

def idents : ESymbols.ByName.Idents :=
  ESymbols.ByName.emptyIdents
  |>.insertIdent! Bool "startStop"
  |>.insertIdent! Bool "reset"
  |>.insertIdent! Bool "risingStartStop"
  |>.insertIdent! Bool "risingReset"
  |>.insertIdent! Bool "isCounting"
  |>.insertIdent! Int "counter"

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

end Sw


Smt.test! [ESys.sw.all]
  Smt.setOption Cvc.Option.produceModels
  let sw := Sw.mk
  let steps := 5
  println! "\nrunning k-induction, step(s) := {steps}"
  let ⟨k, sw⟩ ← sw.kInduction steps
  println! "k-induction stopped at {k}"
  println! "sw@{sw.depth}:"
  for line in sw.toLines "  " do
    println! line
/-- info:
running k-induction, step(s) := 5
k-induction stopped at 2
sw@2:
  candidates at 1 {
    no unknown
    invariant: {}
      `0 ≤ counter`: 1-inductive
      `risingReset → counter = 0`: 1-inductive
    }
    falsified: {}
      `always counting`: falsified at 0
      `counter ≠ -7`: falsified at 0
      `counter ≠ 0`: falsified at 0
      `reset → counter = 0`: falsified at 1
      `¬ reset`: falsified at 0
    }
  }
-/
