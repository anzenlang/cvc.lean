/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Actlit
import Cvc.Sys.Candidates
import Cvc.Sys.Unroller



namespace Cvc



inductive AfterZero (α : Nat → Type) : (n : Nat) → Type
| zero : AfterZero α 0
| mk {k} (get : α k) : AfterZero α k.succ

abbrev AfterZero' (α : Type) (n : Nat) := AfterZero (𝕂 α) n

namespace AfterZero
def get {k : Nat} : AfterZero α k.succ → α k | .mk get => get
instance {k az} : CoeDep (AfterZero α k.succ) az (α k) := ⟨az.get⟩

def nextM [Monad m] (next : α n → m (α n.succ)) : AfterZero α n.succ → m (AfterZero α n.succ.succ)
| .mk get => return .mk (← next get)
def next (next : α n → α n.succ) (az : AfterZero α n.succ) : AfterZero α n.succ.succ :=
  az.nextM (m := Id) next

def nextM' [Monad m] (atZero : m α) : AfterZero' α n → m (AfterZero' α n.succ)
| .zero => mk <$> atZero
| .mk val => mk val |> pure

def next' {n : Nat} (az : AfterZero' α n.succ) (next : α → α := id) : AfterZero' α n.succ.succ :=
  az.next next
end AfterZero



structure Sys (State : Symbols Struct) (depth : Nat := 0)
where private mk' ::
  toUnroller : State.Unroller depth
  candidates : Sys.Candidates State depth
  -- initActlit : AfterZero' Actlit depth

namespace Symbols
export Cvc (Sys)
end Symbols

namespace Sys variable [State : Symbols S]

def mk (init : State.StatePred) (step : State.StateRel)
  (candidates : State.NamedPredicates := .empty)
: State.Sys :=
  let unroller := Symbols.Unroller.mk init step
  let candidates := candidates.mapVal Candidate.mkUnknown
  ⟨unroller, .init candidates⟩

protected def depth : (sys : Sys State depth) → Nat := 𝕂 depth

def toLines (sys : Sys State depth) (pref := "") : Array String :=
  sys.candidates.toLines pref

def addCandidate (sys : State.Sys) (name : String) (pred : State.StatePred) : Res State.Sys := do
  let candidate := Candidate.mkUnknown name pred
  let candidates ← sys.candidates.insertUnknown candidate
  return {sys with candidates}

def addCandidates [ForIn Res α (String × State.StatePred)]
  (sys : State.Sys) (candidates : α)
: Res State.Sys := do
  let mut sys := sys
  for (name, pred) in candidates do
    sys ← sys.addCandidate name pred
  return sys

section variable (sys : Sys State depth)

def getUnknownCandidates : Candidate.UnknownMap State depth :=
  sys.candidates.unknown

abbrev isDone : Bool := sys.candidates.isDone

def isNextBaseReady : Bool := sys.candidates.isNextBaseReady
def isNextStepReady : Bool := sys.candidates.isNextStepReady
def isNextReady : Bool := sys.isNextBaseReady ∧ sys.isNextStepReady
def isBaseOver : Bool := sys.isNextBaseReady
def isStepOver : Bool := sys.isNextStepReady

def getStateAt (k : Nat) (h : k < depth := by omega) : State.TermsAt k :=
  sys.toUnroller.trace.get k

def getState0 (sys : Sys State depth.succ) : State.TermsAt 0 :=
  sys.getStateAt 0

def getLatestState (sys : Sys State (k + 1)) : State.TermsAt k :=
  sys.getStateAt k

def unroll (sys : State.Sys depth)
: (h : ¬ sys.isDone := by assumption)
→ Smt (State.Sys depth.succ) := fun _ => do
  let (nextState, toUnroller) ← sys.toUnroller.unroll
  let candidates ← sys.candidates.next nextState
  return ⟨toUnroller, candidates⟩

def checkBase {k : Nat} (sys : State.Sys k.succ)
: (h : ¬ sys.isBaseOver := by assumption)
→ (maxIter : Nat := sys.candidates.unknown.size.succ)
→ Smt (State.Sys k.succ)
| _, maxIter + 1 => do
  let activators ←
    #[] |> sys.candidates.addBaseActivators
  let candidates ← sys.toUnroller.checkSatBaseAnd activators
    (ifSat := sys.toUnroller.extractCexTrace >>= sys.candidates.registerBaseCex)
    (ifUnsat := sys.candidates.registerBaseUnsat)
  let sys := {sys with candidates}
  if h : sys.isBaseOver then return sys else sys.checkBase h maxIter
| _, 0 => Error.throwInternal s!"\
  base-checking at `{k}` not done after number-of-candidates-plus-one iterations\
"

def checkStep {k : Nat} (sys : State.Sys k.succ.succ)
: (h : ¬ sys.isStepOver := by assumption)
→ (maxIter : Nat := sys.candidates.unknown.size)
→ (maxIterRef : Nat := sys.candidates.unknown.size)
→ Smt (State.Sys k.succ.succ)
| _, maxIter + 1, maxIterRef => do
  let activators ←
    #[] |> sys.candidates.addStepActivators
  let (wasSat, candidates) ← sys.toUnroller.checkSatStepAnd activators
    (ifSat := (true, ·) <$> sys.candidates.registerStepCex)
    (ifUnsat := (false, ·) <$> sys.candidates.registerStepUnsat)
  let sys := {sys with candidates}
  if sys.isDone then
    return sys
  if h : sys.isStepOver then
    return sys
  else if ¬ wasSat then
    Error.throwInternal s!"step not over but step-check returned `unsat`"
  else
    sys.checkStep h maxIter
| _, 0, _maxIterRef =>
  -- return sys
  let info : String := sys.candidates.unknown.foldl (fun acc _ unk => s!" {acc}{unk},") "unknows:"
  Error.throwInternal s!"\
    step-checking at {k.succ} not done after number-of-candidates (`{_maxIterRef}`) iteration(s) | {info}\
  "

def unrollCheckBaseStep {k : Nat} (sys : State.Sys k)
: (h_base : sys.isBaseOver := by assumption)
→ (h_step : sys.isStepOver := by assumption)
→ (h : ¬ sys.isDone := by assumption)
→ Smt (State.Sys k.succ) := fun _ _ _ => do
  let mut sys ← sys.unroll
  if h : ¬ sys.isBaseOver then
    sys ← sys.checkBase
  else Error.throwInternal s!"\
    [unreachable] system `sys` is `¬ sys.isDone`, but verifies `sys.isBaseOver` after unrolling\
  "
  by
    cases k ; exact return sys
    exact
      if sys.isDone then pure sys
      else if h : ¬ sys.isStepOver then sys.checkStep
      else Error.throwInternal s!"\
        [unreachable] system `sys` is `¬ sys.isDone`, but it is `sys.isStepOver` before step-check\
      "

def kInduction {k} (sys : State.Sys k)
: (maxSteps : Nat) → Smt ((k' : Nat) × State.Sys k')
| maxSteps + 1 => do
  if h_sys : sys.isDone then return ⟨k, sys⟩ else
    if h : sys.isBaseOver ∧ sys.isStepOver then
      let ⟨_, _⟩ := h
      let sys ← sys.unrollCheckBaseStep
      if sys.isDone then return ⟨k.succ, sys⟩ else
        let desc := match (sys.isBaseOver, sys.isStepOver) with
          | (false, false) => some "neither base nor step are"
          | (true, false) => "step is"
          | (false, true) => "base is"
          | (true, true) => none
        if let some desc := desc then
          Error.throwInternal s!"after `unrollCheckBaseStep` {k} → {k.succ}, {desc} not over"
        sys.kInduction maxSteps
    else
      let desc := match h' : (sys.isBaseOver, sys.isStepOver) with
        | (false, false) => "neither base nor step are"
        | (true, false) => "step is"
        | (false, true) => "base is"
        | (true, true) => by simp at h' ; contradiction
      Error.throwInternal s!"will not run `kInduction`: {desc} not ready at {k}"
| 0 => return ⟨k, sys⟩

end

end Sys
