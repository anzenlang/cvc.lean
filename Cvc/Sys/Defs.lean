/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Actlit
import Cvc.Sys.Unroller



namespace Cvc

namespace Symbols

inductive Status (State : Symbols S)
| initValidUntil (k? : Option Nat) (stepCex? : Option Nat)
| invariant (k : Nat) (strength : RBSet String)
| cex (k : Nat) (trace : State.ValTrace k.succ)

namespace Status variable [State : Symbols Struct]

def mkCex {k : Nat} (trace : State.ValTrace k.succ) : State.Status :=
  .cex k trace

protected def toString : State.Status → String
| initValidUntil k? stepCex? =>
  s!"Status [[ init valid until {k?.map Nat.pred} | stepCex? = {stepCex?.map Nat.pred} ]]"
| invariant k set =>
  let suff := if set.isEmpty then "" else s!", strengthened by {set.size} lemma(s)"
  s!"Status [[ invariant {k}{suff} ]]"
| cex k _trace => s!"Status [[ cex {k} ]]"

instance : ToString State.Status := ⟨Status.toString⟩

def unknown : State.Status := .initValidUntil none none

def unknownInfo? : State.Status → Option (Option Nat × Option Nat)
| .initValidUntil k? stepCex? => (k?, stepCex?)
| .invariant .. | .cex .. => none

def isUnknown (status : State.Status) : Bool := status.unknownInfo?.isSome

def isStepUnknownAt (k : Nat) : State.Status → Bool
| .initValidUntil _ none => true
| .initValidUntil _ (some k') => k' < k
| .invariant .. | .cex .. => false

def initValidUntil? : State.Status → Option (Option Nat)
| .initValidUntil k? _ => k?
| .invariant .. | .cex .. => none

def updateInitValidUntil [Monad m]
  (initValidDo : Option Nat → m (Option Nat) := pure)
  (stepCexDo : Option Nat → m (Option Nat) := pure)
: State.Status → m State.Status
| .initValidUntil k? stepCex? =>
  return .initValidUntil (← initValidDo k?) (← stepCexDo stepCex?)
| self@(.invariant ..) | self@(.cex ..) => return self

end Status



structure Candidate (State : Symbols Struct) where
private mk' ::
  name : String
  pred : State.StatePred
  currentNegPred : Formula
  currentNegActlit : Actlit
  posActlit : Actlit
  status : State.Status

abbrev Candidates (State : Symbols Struct) := Array State.Candidate

namespace Candidate variable [State : Symbols Struct]

def mk
  (name : String) (pred : {k : Nat} → State.PredAt k) (state0 : State.TermsAt 0)
: Smt State.Candidate := do
  let currentNegPred ← (← pred state0).not
  let currentNegActlit ← Actlit.fresh
  let posActlit ← Actlit.fresh
  currentNegPred.activate currentNegActlit
  return ⟨name, pred, currentNegPred, currentNegActlit, posActlit, Status.unknown⟩

section variable (self : State.Candidate)

def unknownInfo? := self.status.unknownInfo?
def isUnknown := self.status.isUnknown
def isStepUnknownAt := self.status.isStepUnknownAt
def initValidUntil? := self.status.initValidUntil?

def isFalsified : Smt.Sat Bool := self.currentNegPred.getVal

def getCex : Option ((k : Nat) × State.ValTrace k.succ) :=
  match self.status with
  | .cex k trace => some ⟨k, trace⟩
  | .invariant .. | .initValidUntil .. => none

end

def updateInitValidUntil [Monad m]
  (self : State.Candidate)
  (initValidDo : Option Nat → m (Option Nat) := pure)
  (stepCexDo : Option Nat → m (Option Nat) := pure)
: m State.Candidate := do
  let status ← self.status.updateInitValidUntil initValidDo stepCexDo
  return {self with status}

end Candidate

end Symbols



structure Sys (State : Symbols Struct) (k : Nat) extends toUnroller : State.Unroller k where
private mk' ::
  candidates : State.Candidates := #[]

namespace Symbols
export Cvc (Sys)
end Symbols

namespace Sys variable [State : Symbols S]

def mk
  (init : State.StatePred) (step : State.StateRel)
  (namedCandidates : Array (String × State.StatePred))
: Smt (State.Sys 0) := do
  let unroller ← Symbols.Unroller.mk init step
  let state0 := unroller.getTermsLast
  let mut candidates := Array.mkEmpty namedCandidates.size
  for (name, pred) in namedCandidates do
    let candidate ← Symbols.Candidate.mk name pred state0
    candidates := candidates.push candidate
  return ⟨unroller, candidates⟩

section variable (sys : Sys State k)

def getUnknownCandidates : State.Candidates :=
  sys.candidates.filter Symbols.Candidate.isUnknown

def getJustProved : State.Candidates :=
  sys.candidates.filter fun candidate =>
    match candidate.status with
    | .invariant k' _ => k = k'
    | .initValidUntil .. | .cex .. => false

def getFalsifiedAt (depth : Nat) : Array (State.Candidate × State.ValTrace depth.succ) :=
  sys.candidates.filterMap fun candidate =>
    candidate.getCex >>= fun ⟨k', trace⟩ =>
      if h : k' = depth then some (candidate, h ▸ trace) else none

def countUnknownCandidates : Nat := Id.run do
  let mut count := 0
  for c in sys.candidates do
    if c.isUnknown then count := count + 1
  return count

abbrev isDone : Bool := sys.countUnknownCandidates = 0

def activeOldestNegativeCandidates
  (nextState : State.TermsAt k.succ)
: (h : ¬ sys.isDone := by assumption) → Smt Unit := fun _ =>
  for candidate in sys.candidates do
    if candidate.isUnknown then
      let pred ← candidate.pred nextState
      pred.activate candidate.posActlit

def unroll (sys : State.Sys k)
: (h : ¬ sys.isDone := by assumption) → Smt (State.Sys k.succ) := fun _ => do
  let (nextState, toUnroller) ← sys.toUnroller.unroll
  sys.activeOldestNegativeCandidates (by
    simp [Symbols.Unroller.length] at nextState
    exact nextState
  )
  return {sys with toUnroller}

def registerCex (init : Bool) : Smt.Sat (State.Sys k) := do
  let candidates ← sys.candidates.mapM fun candidate => do
    if let some (initK?, stepCexK?) := candidate.unknownInfo? then
      if ¬ (← candidate.isFalsified) then
        return candidate
      -- sanity
      if init then
        if let some initK := initK? then
          if k.succ ≤ initK then
            Error.throwInternal s!"\
              extracting init CEX at {k} but `{candidate.name}` is init-confirmed at {initK}\
            "
          else if k.succ ≠ initK.succ then
            Error.throwInternal s!"\
              extracting init CEX at {k} but `{candidate.name}` is only init-confirmed at {initK}\
            "
      else
        if let some stepCexK := stepCexK? then
          if k.succ ≤ stepCexK then
            Error.throwInternal s!"\
              extracting step CEX at {k} \
              but a step CEX at {stepCexK} exists for candidate `{candidate.name}`\
            "
      if init then
        let cex ← sys.extractCexTrace
        pure {candidate with status := .mkCex cex}
      else pure {candidate with status := .initValidUntil initK? k.succ}
    else pure candidate
  return {sys with candidates}

def registerNoInitCex
: (h : ¬ sys.isDone := by assumption) → Smt.Unsat (State.Sys k) := fun _ => do
  let candidates ← sys.candidates.mapM fun candidate =>
    candidate.updateInitValidUntil (initValidDo := fun old => do
      let expected := if let preK + 1 := k then some preK else none
      if old ≠ expected then
        Error.throwInternal s!"\
          cannot register no-init-cex for `{candidate.name}` at {k}: \
          expected valid-init status `{expected}` but found `{old}`\
        "
      pure k
    )
  return {sys with candidates}

def registerNoStepCex (sys : State.Sys k.succ)
: (h_not_done : ¬ sys.isDone := by assumption) → Smt.Unsat (State.Sys k.succ) := fun _ => do
  let candidates ← sys.candidates.mapM fun candidate => do
    match candidate.unknownInfo? with
    | none => pure candidate
    | some (k?, badAtStep?) =>
      let confirmed := badAtStep?.map (Nat.blt · k.succ) |>.getD true
      if confirmed then
        if k?.map (k.ble ·) |>.getD false then
          Error.throwInternal s!"\
            cannot register no-step-cex for `{candidate.name}` at {k.succ}: \
            expected valid-init status `≥ {k}` but found `{k?}`\
          "
        else pure {candidate with status := .invariant k RBSet.empty}
      else pure candidate
  return {sys with candidates}

def getInitActlits : (h : ¬ sys.isDone := by assumption) → Array (Term Bool) := fun _ => Id.run do
  let mut actlits := #[]
  for candidate in sys.candidates do
    if let some (initK?, _) := candidate.unknownInfo? then
      let ignore := initK?.map (k.blt ·) |>.getD false
      if ¬ ignore then
        actlits := actlits.push ↑candidate.currentNegActlit
  return actlits

def getStepActlits : (h : ¬ sys.isDone := by assumption) → Array (Term Bool) := fun _ => Id.run do
  let mut actlits := #[]
  for candidate in sys.candidates do
    if let some (_, stepCexK?) := candidate.unknownInfo? then
      let ignore := stepCexK?.map (k.blt ·) |>.getD false
      if ¬ ignore then
        actlits :=
          actlits.push ↑candidate.currentNegActlit |>.push ↑candidate.posActlit
  return actlits

def checkInit (sys : State.Sys k)
: (h : ¬ sys.isDone := by assumption)
→ (maxIter : Nat := sys.candidates.size.succ)
→ Smt (State.Sys k)
| _, maxIter + 1 => do
  let actlits := sys.getInitActlits
  if actlits.isEmpty then
    return sys
  let (gotCex, sys) ← sys.toUnroller.checkSatAnd (init := true) actlits
    (ifSat := (true, ·) <$> sys.registerCex (init := true))
    (ifUnsat := (false, ·) <$> sys.registerNoInitCex)
  if gotCex then
    if h : ¬ sys.isDone then sys.checkInit h maxIter else return sys
  else return sys
| _, 0 => Error.throwInternal s!"\
  init-checking at {k} not done after {sys.candidates.size.succ} iteration(s)\
"

def checkStep (sys : State.Sys k.succ)
: (h : ¬ sys.isDone := by assumption)
→ (maxIter : Nat := sys.candidates.size.succ)
→ Smt (State.Sys k.succ)
| _, maxIter + 1 => do
  let actlits := sys.getStepActlits
  if actlits.isEmpty then
    return sys
  let (gotCex, sys) ← sys.toUnroller.checkSatAnd (init := false) actlits
    (ifSat := (true, ·) <$> sys.registerCex (init := false))
    (ifUnsat := (false, ·) <$> sys.registerNoStepCex)
  if gotCex then
    if h : ¬ sys.isDone then sys.checkStep h maxIter else
      -- #TODO prove this can't happen
      Error.throwInternal "🙀 CEX registration changed the *not-done* status of the system 🙀"
  else return sys
| _, 0 => Error.throwInternal s!"\
  step-checking at {k.succ} not done after {sys.candidates.size.succ} iteration(s)\
"

def check : (h : ¬ sys.isDone := by assumption) → Smt (Option $ State.Sys k.succ) := fun _ => do
  let sys ← sys.checkInit
  if h : ¬ sys.isDone then
    let sys ← sys.unroll
    if h : ¬ sys.isDone then sys.checkStep else
      -- #TODO prove this can't happen
      Error.throwInternal "🙀 `unrollOnce` changed `isDone` value 🙀"
  else
    return none

def kInduction {k} (sys : State.Sys k) : (maxSteps : Nat) → Smt ((k' : Nat) × State.Sys k')
| maxSteps + 1 => do
  if h : sys.isDone then return ⟨k, sys⟩ else
    let sys ← sys.checkInit
    if h : sys.isDone then return ⟨k, sys⟩ else
      let sys ← sys.unroll
      let sys ← if h : ¬ sys.isDone then sys.checkStep else
        -- #TODO prove this can't happen
        Error.throwInternal "🙀 `unrollOnce` changed `isDone` value 🙀"
      if h : sys.isDone then return ⟨k.succ, sys⟩ else
        sys.kInduction maxSteps
| 0 => return ⟨k, sys⟩

end

end Sys
