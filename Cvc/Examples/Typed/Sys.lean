/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

meta import Cvc.Typed.Extra.Sys

import Cvc.Typed.Extra.Sys
import Cvc.Typed.Theory.Arith



namespace Cvc.Typed.Tests.Bmc variable [Ω]


structure.stateVars Sv where
  startStop : Bool
  reset : Bool
  counting : Bool
  count : Int

def sys : Sys Sv where
  idents := Sv.idents
  init state := smt! state.counting = state.startStop ∧ state.count = 0
  next state state' := smt!
    (state'.counting = if state'.startStop then ¬ state.counting else state.counting)
    ∧ (state'.count = if state'.reset then 0 else state.count + if state'.counting then 1 else 0)
  candidates := #[
    ("0 ≤ count", fun state => smt! 0 ≤ state.count),
    ("reset → count = 0", fun state => smt! state.reset → state.count = 0),
    ("count ≤ 3", fun state => smt! state.count ≤ 3),
    ("count = 3", fun state => smt! state.count = 3),
  ]

def bmc : Env (Sys.Bmc Sv 0) := Sys.Bmc.mk sys

partial def run (bmc : Sys.Bmc Sv k) (ub : Nat := 5) : Env Unit :=
  loop bmc ub
where loop {k} (bmc : Sys.Bmc Sv k) : Nat → Env Unit
| 0 => do
  println! "done @ {k}, {bmc.candidates.size} candidate(s) left"
  for (name, _) in bmc.candidates do
    println! "- {name}"
| n + 1 => do
  if bmc.isDone then
    println! "no candidates left, done"
    return ()
  println! "\nchecking at {k}"
  if let some (falsified, bmc) ← bmc.check then
    println! "{falsified.size} candidate(s) falsified at {k}"
    for name in falsified do
      println! "- {name}"
    let some cex := bmc.falsified[0]?
      | throwInternal "expected cex"
    println! "cex"
    cex.2.1.iterM fun {k} values => do
      println! "- @{k} \{ \
        cnt := {values.count}, \
        cnt? := {values.counting}, \
        ss := {values.startStop}, \
        reset := {values.reset} \
      }"
    loop bmc n.succ
  else loop (← bmc.unroll) n

/--
info:
checking at 0
1 candidate(s) falsified at 0
- count = 3
cex
- @0 { cnt := 0, cnt? := false, ss := false, reset := false }

checking at 0

checking at 1

checking at 2

checking at 3

checking at 4
1 candidate(s) falsified at 4
- count ≤ 3
cex
- @0 { cnt := 0, cnt? := false, ss := false, reset := false }
- @1 { cnt := 1, cnt? := true, ss := true, reset := false }
- @2 { cnt := 2, cnt? := true, ss := false, reset := false }
- @3 { cnt := 3, cnt? := true, ss := false, reset := false }
- @4 { cnt := 4, cnt? := true, ss := false, reset := false }

checking at 4
done @ 5, 2 candidate(s) left
- 0 ≤ count
- reset → count = 0
-/
#guard_msgs in #eval Env.runIO do bmc >>= run
