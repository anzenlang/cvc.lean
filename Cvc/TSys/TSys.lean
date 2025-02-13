/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Actlit
import Cvc.TSys.Unroller



namespace Cvc.Safe



namespace Symbols

inductive CandidateStatus (State : Symbols S)
| initValidUntil (k? : Option Nat) (stepCex? : Option Nat)
| invariant (k : Nat) (strength : Set String)
| cex (k : Nat) (trace : State.Unrolling State.Model k)

namespace CandidateStatus

variable {State : Symbols S}

protected def toString : CandidateStatus State → String
| initValidUntil k? stepCex? =>
  s!"Status [[ init valid until {k?.map Nat.pred} | stepCex? = {stepCex?.map Nat.pred} ]]"
| invariant k set =>
  s!"Status [[ invariant {k}, strengthened by {set.size} lemmas ]]"
| cex k _trace =>
  s!"Status [[ cex {k} ]]"

instance : ToString (CandidateStatus State) :=
  ⟨CandidateStatus.toString⟩

def unknownInfo? : CandidateStatus State → Option (Option Nat × Option Nat)
| .initValidUntil k? stepCex? => (k?, stepCex?)
| .invariant _ _ | .cex _ _ => none

def isUnknown (status : CandidateStatus State) : Bool :=
  status.unknownInfo?.isSome

def isStepUnknownAt (k : Nat) : CandidateStatus State → Bool
| .initValidUntil _ none => true
| .initValidUntil _ (some k') => k' < k
| .invariant _ _ | .cex _ _ => false

def initValidUntil? : CandidateStatus State → Option (Option Nat)
| .initValidUntil k? _ => k?
| .invariant _ _ | .cex _ _ => none

def updateInitValidUntil [Monad m]
  (initValidDo : Option Nat → m (Option Nat) := pure)
  (stepCexDo : Option Nat → m (Option Nat) := pure)
: CandidateStatus State → m (CandidateStatus State)
| .initValidUntil k? stepCex? =>
  return .initValidUntil (← initValidDo k?) (← stepCexDo stepCex?)
| self@(.invariant _ _) | self@(.cex _ _) =>
  return self

end CandidateStatus

structure Candidate (State : Symbols S) where
private mkRaw ::
  name : String
  pred : State.Predicate
  currentNegativePred : Term Bool
  currentNegativeActlit : Smt.Actlit
  allOldPositiveActlit : Smt.Actlit
  status : State.CandidateStatus

namespace Candidate

def mk
  {State : Symbols S}
  (name : String) (pred : State.Predicate)
  (stateZero : State.TermsAt 0)
: SmtM State.Candidate := do
  let currentNegativePred ← (← pred stateZero).not
  let currentNegativeActlit ← Cvc.Smt.mkActlit
  let allOldPositiveActlit ← Cvc.Smt.mkActlit
  currentNegativePred.assertActivation currentNegativeActlit

  return {
    name, pred
    currentNegativePred, currentNegativeActlit
    allOldPositiveActlit
    status := CandidateStatus.initValidUntil none none
  }

variable (self : Candidate State)

def unknownInfo? :=
  self.status.unknownInfo?

def isUnknown : Bool :=
  self.status.isUnknown

def isStepUnknownAt (k : Nat) : Bool :=
  self.status.isStepUnknownAt k

def initValidUntil? : Option (Option Nat) :=
  self.status.initValidUntil?

def updateInitValidUntil [Monad m]
  (initValidDo : Option Nat → m (Option Nat) := pure)
  (stepCexDo : Option Nat → m (Option Nat) := pure)
: m (Candidate State) := do
  let status ← self.status.updateInitValidUntil initValidDo stepCexDo
  return { self with status }

def isFalsified : Smt.SatT IO Bool :=
  Smt.getValue self.currentNegativePred

end Candidate



-- structure Candidates (State : Symbols S) where
-- private mkRaw ::
--   unknown : Array State.Candidate
--   falsifiedInit : Array ((k : Nat) × State.CexTrace k × Array State.Candidate)
--   falsifiedStep : Array ((k : Nat) × State.CexTrace k × Array State.Candidate)
--   verifiedInit : Array (Nat × Array State.Candidate)
--   verifiedStep : Array (Nat × Array State.Candidate)

-- namespace Candidates

-- variable {State : Symbols S}

-- def mk
--   (namedCandidates : Array (String × State.Predicate))
--   (svarsZero : State.Terms 0)
-- : SmtM State.Candidates := do
--   let mut unknown := Array.mkEmpty namedCandidates.size
--   for (name, pred) in namedCandidates do
--     let candidate ← Symbols.Candidate.mk name pred svarsZero
--     unknown := unknown.push candidate
--   return ⟨unknown, #[], #[], #[], #[]⟩

-- variable (self : State.Candidates)

-- def registerCex (init : Bool) (unroller : State.Unroller) : Smt.SatM State.Candidates := do
--   let cex ← unroller.extractCexTrace
--   let mut unknown := #[]
--   let mut bad := #[]
--   for candidate in self.unknown do
--     if ← candidate.isFalsified then
--       bad := bad.push candidate
--     else
--       unknown := unknown.push candidate
--   let falsified := ⟨unroller.depthSucc, cex, bad⟩
--   return {self with unknown, falsified}
--   sorry

-- end Candidates

end Symbols



/-- Transition system for some notion of state.

Consider using `Symbols.TSys` instead, which allows `State.TSys` notation when `State : Symbols S`.
-/
structure TSys (State : Symbols S) extends State.Unroller
where private mkRaw ::
  candidates : Array State.Candidate

/-- Transition system over some notion of state. -/
abbrev Symbols.TSys (State : Symbols S) :=
  Safe.TSys State

namespace TSys

variable {State : Symbols S}

/-- Builds a transition system, assumes the solver expects a `Smt.setLogic` command. -/
def mk
  (logic : Logic) (symbols : State.Idents)
  (init : State.Predicate) (step : State.Relation)
  (namedCandidates : Array (String × State.Predicate))
: SmtM State.TSys := do
  let unroller ← Symbols.Unroller.mk logic symbols init step
  let svarsZero := unroller.getCurrentSymbols
  let mut candidates := Array.mkEmpty namedCandidates.size
  for (name, pred) in namedCandidates do
    let candidate ← Symbols.Candidate.mk name pred svarsZero
    candidates := candidates.push candidate
  return ⟨unroller, candidates⟩

variable {State : Symbols S} (sys : TSys State)

def initDepth := sys.depthSucc.pred

def getUnknownCandidates : Array State.Candidate :=
  sys.candidates.filter Symbols.Candidate.isUnknown

def getJustProved : Array State.Candidate :=
  sys.candidates.filter fun candidate =>
    match candidate.status with
    | .invariant k _ => sys.depthSucc = k
    | .initValidUntil _ _ | .cex _ _ => false

def getFalsifiedAt (depth : Nat) : Array (State.Candidate × State.Trace depth.succ) :=
  sys.candidates.filterMap fun candidate =>
    match candidate.status with
    | .cex k' trace =>
      if h : k' = depth.succ then some (candidate, h ▸ trace) else none
    | .invariant _ _ | .initValidUntil _ _ => none

def countUnknownCandidates : Nat := Id.run do
  let mut count := 0
  for c in sys.candidates do
    if c.isUnknown then
      count := count + 1
  return count

abbrev isDone : Bool :=
  sys.countUnknownCandidates = 0

/-- Positively activates **unknown** candidates at `sys.depthSucc`. -/
def activateOldestNegativeCandidates
  (svars : State.TermsAt sys.depthSucc)
: (h : ¬ sys.isDone := by assumption) → SmtM Unit := fun _ =>
  for candidate in sys.candidates do
    if candidate.isUnknown then
      let actlit := candidate.allOldPositiveActlit
      let pred ← candidate.pred svars
      pred.assertActivation actlit

def unroll (sys : State.TSys) : Nat → (h : ¬ sys.isDone := by assumption) → SmtM State.TSys
| 0, _ => return sys
| n + 1, _ => do
  let (svars, toUnroller) ← sys.toUnroller.unrollOnce
  let sys := {sys with toUnroller}
  sys.activateOldestNegativeCandidates svars
  sys.unroll n

def unrollOnce (h : ¬ sys.isDone := by assumption) : SmtM State.TSys :=
  sys.unroll 1 h

def registerCex (inInit : Bool) : Smt.SatT IO State.TSys := do
  let cex ← sys.toUnroller.extractCexTrace
  -- println! "cex"
  -- for ⟨i, svars⟩ in sys.unrolling do
  --   println! "|==| @{i}"
  --   for ⟨_, svar⟩ in svars.state do
  --     let _ := svar.inst
  --     let val ← Smt.getValue svar.get
  --     println! "| {svar.get} = {val}"
  -- println! "|==|"
  let candidates ← sys.candidates.mapM fun candidate => do
    -- println! "  - `{candidate.name}`"
    if let some (initK?, stepCexK?) := candidate.unknownInfo? then
      -- println! "    unknown"
      if ¬ (← candidate.isFalsified) then
        -- println! "    not falsified"
        return candidate
      -- println! "    falsified"
      -- sanity
      if inInit then
        if let some k := initK? then
          if sys.depthSucc ≤ k then
            throw $ .internal s!"\
              extracting init CEX at {sys.depthSucc} but `{candidate.name}` is init-confirmed at {k}\
            "
          else if sys.depthSucc ≠ k.succ then
            throw $ .internal s!"\
              extracting init CEX at {sys.depthSucc} but `{candidate.name}` \
              is only init-confirmed at {k}\
            "
      else
        if let some k := stepCexK? then
          if sys.depthSucc ≤ k then
            throw $ .internal s!"\
              extracting step CEX at {sys.depthSucc} \
              but a step CEX at {k} exists for candidate `{candidate.name}`\
            "
      let candidate ←
        if inInit then
          -- println! "    registering init cex"
          pure {candidate with status := .cex sys.depthSucc cex}
        else
          -- println! "    registering step cex"
          pure {candidate with status := .initValidUntil initK? sys.depthSucc}
      pure candidate
    else
      pure candidate

  return {sys with candidates}

def registerNoInitCex
: (h : ¬ sys.isDone := by assumption) → Smt.UnsatM State.TSys := fun _ => do
  let candidates ← sys.candidates.mapM fun candidate =>
    candidate.updateInitValidUntil (initValidDo := fun old => do
      let expected := if let d + 1 := sys.initDepth then some d.succ else none
      if old ≠ expected then
        throw $ .internal s!"\
          cannot register no-init-cex for `{candidate.name}` at {sys.initDepth}: \
          expected valid-init status `{expected}` but found `{old}`\
        "
      pure sys.depthSucc
    )
  return { sys with candidates }

def registerNoStepCex
  (h_depth : 0 < sys.depthSucc := by first | assumption | omega)
: (h_not_done : ¬ sys.isDone := by assumption) → Smt.UnsatT IO State.TSys := fun _ => do
  -- println! "  - registerNoStepCex"
  let candidates ← sys.candidates.mapM fun candidate => do
    -- println! "    - `{candidate.name}`"
    match candidate.unknownInfo? with
    | none => pure candidate
    | some (k?, badAtStep?) =>
      -- println! "      unknown info: {k?}, {badAtStep?}"
      let confirmed :=
        badAtStep?.map (fun k => k.blt sys.depthSucc) |>.getD true
      if confirmed then
        let expected := match h_depth_val : sys.depthSucc with
          | 0 => by simp only [h_depth_val, Nat.lt_irrefl] at h_depth
          | d + 1 => some d
        if expected ≠ k? then
          throw $ .internal s!"\
            cannot register no-step-cex for `{candidate.name}` at {sys.depthSucc}: \
            expected valid-init status `{expected}` but found `{k?}`\
          "
        else
          pure { candidate with status := .invariant sys.depthSucc Set.empty }
      else
        pure candidate
  return { sys with candidates }

def getInitActlits : (h : ¬ sys.isDone := by assumption) → Array (Term Bool) := fun _ => Id.run do
  let mut actlits := #[]
  for c in sys.candidates do
    if let some (initK?, _) := c.unknownInfo? then
      let ignore := initK?.map (sys.depthSucc ≤ · : Nat → Bool) |>.getD false
      if ¬ ignore then
        actlits :=
          Term.ofActlit c.currentNegativeActlit
          |> actlits.push
  return actlits

def getStepActlits : (h : ¬ sys.isDone := by assumption) → Array (Term Bool) := fun _ => Id.run do
  let mut actlits := #[]
  for c in sys.candidates do
    if let some (_, stepCexK?) := c.unknownInfo? then
      let ignore := stepCexK?.map (sys.depthSucc ≤ · : Nat → Bool) |>.getD false
      if ¬ ignore then
        actlits :=
          Term.ofActlit c.currentNegativeActlit
          |> actlits.push
          |>.push (Term.ofActlit c.allOldPositiveActlit)
  return actlits

partial
def checkInit (sys : State.TSys) (h : ¬ sys.isDone := by assumption) : SmtIO State.TSys := do
  let actlits := sys.getInitActlits
  if actlits.isEmpty then
    return sys
  let (gotCex, sys) ← sys.toUnroller.checkSat (inInit := true) actlits
    (ifSat := do
      let sys ← sys.registerCex (inInit := true)
      return (true, sys))
    (ifUnsat := do
      let sys ← sys.registerNoInitCex
      return (false, sys))
  if gotCex then
    if h : ¬ sys.isDone then
      sys.checkInit
    else
      return sys
  else
    return sys

partial
def checkStep
  (sys : State.TSys)
  (h_depth : 0 < sys.depthSucc := by first | assumption | omega)
  (h_not_done : ¬ sys.isDone := by assumption)
: SmtIO State.TSys := do
  let actlits := sys.getStepActlits
  if actlits.isEmpty then
    return sys
  let (gotCex, sys) ← sys.toUnroller.checkSat (inInit := false) actlits
    (ifSat := do
      -- println! "  sat"
      let sys ← sys.registerCex (inInit := false)
      return (true, sys))
    (ifUnsat := do
      -- println! "  unsat"
      let sys ← sys.registerNoStepCex
      return (false, sys))
  if gotCex then
    if h_not_done : ¬ sys.isDone then
      if h_depth : 0 < sys.depthSucc then
        sys.checkStep
      else
        -- #TODO prove this can't happen
        throw $ .internal s!"🙀 CEX registration changed the depth of the unroller 🙀"
    else
      -- #TODO prove this can't happen
      throw $ .internal s!"🙀 CEX registration changed the *not-done* status of the system 🙀"
  else
    return sys

def check
  (sys : State.TSys)
: (h : ¬ sys.isDone := by assumption)
→ SmtIO State.TSys
:= fun _ => do
  let sys ← sys.checkInit
  if h : ¬ sys.isDone then
    let sys ← sys.unrollOnce
    if h : ¬ sys.isDone then
      if h' : 0 < sys.depthSucc then
        let sys ← sys.checkStep
        return sys
      else
        -- #TODO prove this can't happen
        throw $ .internal s!"🙀 `unrollOnce`'s result does not verify `0 < depth` 🙀"
    else
      -- #TODO prove this can't happen
      throw $ .internal s!"🙀 `unrollOnce` changed `isDone` value 🙀"
  else
    return sys

end TSys
