import Cvc.TSys.TSys

import CvcTest.Safe.Init



namespace Cvc.Safe.TSys.Test.Sw1

open scoped Cvc.Safe.Test



structure State.Vars (F : Type → Type) : Type where
  startStop : SVar F Bool
  reset : SVar F Bool
  counting : SVar F Bool
  count : SVar F Int

namespace State.Vars
variable (self : Vars F)

def startStop! := self.startStop.get
def reset! := self.reset.get
def counting! := self.counting.get
def count! := self.count.get
end State.Vars

scoped macro "returnIfDone! " t:term:max otherwise:term : term => `(
  do
    match ← $t with
    | .yield acc => acc |> ($otherwise)
    | .done res => pure res
)

instance State : SVars State.Vars where
  mapM self f := do
    return {
      startStop := ← f self.startStop
      reset := ← f self.reset
      counting := ← f self.counting
      count := ← f self.count
    }
  forIn self acc f := do
    returnIfDone! (f self.startStop.untype acc) fun acc =>
    returnIfDone! (f self.reset.untype acc) fun acc =>
    returnIfDone! (f self.counting.untype acc) fun acc =>
    returnIfDone! (f self.count.untype acc) fun acc =>
      pure acc

def State.symbols : State.Symbols :=
  ⟨"startStop", "reset", "counting", "count"⟩

def State.init : State.Predicate :=
  smtfun state =>
    state.count! = 0 ∧ ¬ state.counting!

def State.step : State.Relation :=
  smtfun state state' =>
    state'.counting! = (
      if state'.startStop! then ¬ state.counting! else state.counting!
    ) ∧ state'.count! = (
      if state'.reset! then 0
      else if state'.counting! then state.count! + 1 else state.count!
    )

def State.candidateZeroLtCount : String × State.Predicate := (
  "zeroLtCount",
  smtfun state => 0 < state.count!
)

def State.candidateCountPos : String × State.Predicate := (
  "countPos",
  smtfun state => 0 ≤ state.count!
)

def State.candidateResetInv : String × State.Predicate := (
  "resetInv",
  smtfun state => state.reset! → state.count! = 0
)

def State.candidateCountNeqN7 : String × State.Predicate := (
  "CountNeqN7",
  smtfun state => state.count! ≠ - 7
)

def State.candidateCountNeq7 : String × State.Predicate := (
  "CountNeq7",
  smtfun state => state.count! ≠ 7
)

abbrev Sys := State.TSys

namespace Sys

def mkBad : SmtM Sys :=
  TSys.mk .qf_lia State.symbols State.init State.step
    #[State.candidateZeroLtCount]

def mkBadFar : SmtM Sys :=
  TSys.mk .qf_lia State.symbols State.init State.step
    #[State.candidateCountNeq7]

def mkBasic : SmtM Sys :=
  TSys.mk .qf_lia State.symbols State.init State.step
    #[State.candidateCountPos]

def mkStrong : SmtM Sys :=
  TSys.mk .qf_lia State.symbols State.init State.step
    #[State.candidateCountPos, State.candidateResetInv, State.candidateCountNeqN7]

def mkWeak : SmtM Sys :=
  TSys.mk .qf_lia State.symbols State.init State.step
    #[State.candidateResetInv]

/--

# TODO

- provably terminating, needs `(← sys.check).depth = sys.depth.succ` to prove `sys.depth - k`
  decreases
-/
def runUntil (sys : Sys) : (k : Nat) → SmtT IO Unit
| 0 => do
  println! "done, but really done?: {sys.isDone}"
  return ()
| k + 1 => do
  if h : sys.isDone then
    println! "\nnothing left to do at depth {sys.depth}/{k}"
    return ()
  else
    println! "\ncurrently at {sys.depth}"
    let sys ← sys.check
    println! "- check done, now at {sys.depth}"
    for candidate in sys.candidates do
      println! "  {candidate.name} → {candidate.status}"
    let provedJustNow := sys.getJustProved
    if ¬ provedJustNow.isEmpty then
      println! "- just proved"
      for c in provedJustNow do
        println! "  - `{c.name}`"
    else
      println! "- failed to prove anything"
    let cexJustNow := sys.getFalsifiedAt sys.depth
    if ¬ cexJustNow.isEmpty then
      println! "- just falsified"
      for (c, cex) in cexJustNow do
        println! "\n  - `{c.name}`"
        let s := cex.toString sys.symbols (pref := "    ")
        println! "{s}"
    else
      println! "- no cex found"
    runUntil sys k

def showNegCandidates (sys : Sys) (pref := "") : IO Unit := do
  for candidate in sys.candidates do
    let term := candidate.currentNegativePred
    println! "{pref}`¬ {candidate.name}` = {term}"

end Sys

def run (mkSys : SmtM Sys) (ub : Nat := 10) (showNegCandidates := false) : SmtT IO Unit := do
  println! ""
  println! "creating system..."
  let sys ← mkSys
  if showNegCandidates then
    println! "candidates:"
    sys.showNegCandidates "- "
  sys.runUntil ub
  println! "exiting"



/-- info:
creating system...

currently at 0
- check done, now at 0
  zeroLtCount → Status [[ cex 1 ]]
- failed to prove anything
- just falsified

  - `zeroLtCount`
    |===| state 0
    | startStop = false
    | reset = false
    | counting = false
    | count = 0
    |===|

nothing left to do at depth 0/8
exiting
-/
#test do
  run Sys.mkBad
    -- (showNegCandidates := true)



/-- info:
creating system...

currently at 0
- check done, now at 1
  countPos → Status [[ invariant 2, strengthened by 0 lemmas ]]
- just proved
  - `countPos`
- no cex found

nothing left to do at depth 1/8
exiting
-/
#test do
  run Sys.mkBasic
    -- (showNegCandidates := true)



/-- info:
creating system...

currently at 0
- check done, now at 1
  resetInv → Status [[ invariant 2, strengthened by 0 lemmas ]]
- just proved
  - `resetInv`
- no cex found

nothing left to do at depth 1/8
exiting
-/
#test do
  run Sys.mkWeak
    -- (showNegCandidates := true)



/-- info:
creating system...

currently at 0
- check done, now at 1
  countPos → Status [[ invariant 2, strengthened by 0 lemmas ]]
  resetInv → Status [[ invariant 2, strengthened by 0 lemmas ]]
  CountNeqN7 → Status [[ invariant 2, strengthened by 0 lemmas ]]
- just proved
  - `countPos`
  - `resetInv`
  - `CountNeqN7`
- no cex found

nothing left to do at depth 1/8
exiting
-/
#test do
  run Sys.mkStrong
    -- (showNegCandidates := true)



/-- info:
creating system...

currently at 0
- check done, now at 1
  CountNeq7 → Status [[ init valid until (some 0) | stepCex? = (some 1) ]]
- failed to prove anything
- no cex found

currently at 1
- check done, now at 2
  CountNeq7 → Status [[ init valid until (some 1) | stepCex? = (some 2) ]]
- failed to prove anything
- no cex found

currently at 2
- check done, now at 3
  CountNeq7 → Status [[ init valid until (some 2) | stepCex? = (some 3) ]]
- failed to prove anything
- no cex found

currently at 3
- check done, now at 4
  CountNeq7 → Status [[ init valid until (some 3) | stepCex? = (some 4) ]]
- failed to prove anything
- no cex found

currently at 4
- check done, now at 5
  CountNeq7 → Status [[ init valid until (some 4) | stepCex? = (some 5) ]]
- failed to prove anything
- no cex found

currently at 5
- check done, now at 6
  CountNeq7 → Status [[ init valid until (some 5) | stepCex? = (some 6) ]]
- failed to prove anything
- no cex found

currently at 6
- check done, now at 7
  CountNeq7 → Status [[ init valid until (some 6) | stepCex? = (some 7) ]]
- failed to prove anything
- no cex found

currently at 7
- check done, now at 7
  CountNeq7 → Status [[ cex 8 ]]
- failed to prove anything
- just falsified

  - `CountNeq7`
    |===| state 7
    | startStop = false
    | reset = false
    | counting = true
    | count = 7
    |===| state 6
    | startStop = false
    | reset = false
    | counting = true
    | count = 6
    |===| state 5
    | startStop = false
    | reset = false
    | counting = true
    | count = 5
    |===| state 4
    | startStop = false
    | reset = false
    | counting = true
    | count = 4
    |===| state 3
    | startStop = false
    | reset = false
    | counting = true
    | count = 3
    |===| state 2
    | startStop = false
    | reset = false
    | counting = true
    | count = 2
    |===| state 1
    | startStop = true
    | reset = false
    | counting = true
    | count = 1
    |===| state 0
    | startStop = false
    | reset = false
    | counting = false
    | count = 0
    |===|

nothing left to do at depth 7/1
exiting
-/
#test do
  run Sys.mkBadFar
    -- (showNegCandidates := true)