/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Actlit
import Cvc.Symbols
import Cvc.Sys.Trace



namespace Cvc



namespace Sys

namespace Candidate

structure Info (State : Symbols S) where
  name : String
  pred : State.StatePredicate

inductive Status (State : Symbols S) (α : Nat → Type) : (depth : Nat) → Type
| init (info : Info State) : Status State α 0
| mk (info : Info State) (data : α k) : Status State α k.succ

namespace Status

def info : Status State α depth → Info State
| .init info .. | .mk info .. => info

def decons {k : Nat} : Status State α k.succ → Info State × α k
| .mk info data => (info, data)

def data {k : Nat} (status : Status State α k.succ) : α k :=
  status.decons.snd

private def updateData {k : Nat} (data : α k) : Status State α k.succ → Status State α k.succ
| .mk info _ => .mk info data

section variable (status : Status State α depth)
def name : String := status.info.name
def pred : State.StatePredicate := status.info.pred
end

protected def toString [∀ k, ToString (α k)] : Status State α depth → String
| .init info => s!"`{info.name}`: init"
| .mk info data => s!"`{info.name}`: {data}"

instance [∀ k, ToString (α k)] : ToString (Status State α depth) := ⟨Status.toString⟩

end Status



structure Invariant.Data (State : Symbols S) (k : Nat) where
  provedAt : Nat
  posActlit : Actlit
  withCandidates : Array String
  withLemmas : Array State.Predicate

namespace Invariant.Data

def next (info : Info State) (nextState : State.TermsAt k.succ)
: Invariant.Data State k
→ (activate : Bool := true)
→ Smt (Invariant.Data State k.succ)
| ⟨provedAt, posActlit, withCandidates, withLemmas⟩, activate => do
  if activate then
    let nextPred ← info.pred nextState
    posActlit.activate nextPred
  return ⟨provedAt, posActlit, withCandidates, withLemmas⟩

protected def toString (data : Data State k) : String :=
  s!"{data.provedAt}-inductive"

instance : ToString (Data State k) := ⟨Data.toString⟩

end Invariant.Data

abbrev Invariant (State : Symbols S) := Status State (Invariant.Data State)

namespace Invariant

protected def toString (inv : Invariant State depth) : String :=
  toString inv

def next {k : Nat} (nextState : State.TermsAt k.succ)
: Invariant State k.succ → Smt (Invariant State k.succ.succ)
| .mk info data => return .mk info (← data.next info nextState)

end Invariant



structure Falsified.Data (State : Symbols S) (k : Nat) where
  negActlit : Actlit
  falsifiedAt : Nat
  cex : State.ValTrace falsifiedAt.succ

namespace Falsified.Data

def next (info : Info State) (state : State.TermsAt k.succ)
: Falsified.Data State k → Smt (Falsified.Data State k.succ)
| ⟨negActlit, falsifiedAt, cex⟩ => do
  let nextPred ← info.pred state
  negActlit.activate nextPred
  return ⟨negActlit, falsifiedAt, cex⟩

protected def toString (data : Data State k) : String :=
  s!"falsified at {data.falsifiedAt}"

instance : ToString (Data State k) := ⟨Data.toString⟩

end Falsified.Data

abbrev Falsified (State : Symbols S) := Status State (Falsified.Data State)

namespace Falsified

protected def toString (fls : Falsified State depth) : String :=
  toString fls

def next {k : Nat} (state : State.TermsAt k.succ)
: Falsified State k.succ → Smt (Falsified State k.succ.succ)
| .mk info data => return .mk info (← data.next info state)

end Falsified

structure Unknown.Data (State : Symbols S) (k : Nat) where
  posActlit : Actlit
  currNegActlit : Actlit
  currPred : Formula
  baseValidUpTo : Option Nat
  stepInvalidUpTo : Option Nat
  stepValidAt : Option Nat

namespace Unknown.Data

private def init (info : Info State) (nextState : State.TermsAt 0)
: Smt (Unknown.Data State 0) := do
  let posActlit ← Actlit.fresh
  let currNegActlit ← Actlit.fresh
  let currPred ← info.pred nextState
  currNegActlit.activate (← currPred.not)
  return ⟨posActlit, currNegActlit, currPred, none, none, none⟩

protected def toString (data : Data State k) : String :=
  s!"\
    baseValidUpTo: {data.baseValidUpTo}, \
    stepInvalidUpTo: {data.stepInvalidUpTo}, \
    stepValidAt: {data.stepValidAt}\
  "

instance : ToString (Data State k) := ⟨Data.toString⟩

def isBaseValid (data : Unknown.Data State k) : Bool :=
  data.baseValidUpTo = some k

def isStepInvalid (data : Unknown.Data State k) : Bool :=
  data.stepInvalidUpTo = some k

def isInvariant? (data : Unknown.Data State k) : Option Nat := do
  let baseK ← data.baseValidUpTo
  let stepK ← data.stepValidAt
  if stepK ≤ baseK.succ then return stepK else none

def toInvariant? (data : Unknown.Data State k) : Option (Invariant.Data State k) := do
  let invK ← data.isInvariant?
  return ⟨invK, data.posActlit, #[], #[]⟩

private def confirmBase (data : Unknown.Data State k) : Res (Unknown.Data State k) := do
  if let some prev_k := data.baseValidUpTo then
    if prev_k.succ = k then return {data with baseValidUpTo := k} else
      Error.throwUser
        s!"cannot confirm base at `{k}`: \
        currently only confirmed at `{prev_k}` with `{prev_k} + 1 ≠ {k}`"
  else
    if k = 0 then return {data with baseValidUpTo := k} else
      Error.throwUser
        s!"cannot confirm base at `{k}`: \
        currently unconfirmed for any `k` and `{k} ≠ 0`"

private def confirmStep {k : Nat} (data : Unknown.Data State k.succ)
: Res (Unknown.Data State k.succ) :=
  if let some prev_k := data.stepValidAt then
    Error.throwUser s!"will not confirm step at `{k}`: already confirmed at `{prev_k}`"
  else return {data with stepValidAt := k}

private def invalidStep {k : Nat} (data : Unknown.Data State k.succ)
: Res (Unknown.Data State k.succ) :=
  if let some prev_k := data.stepValidAt then
    Error.throwUser s!"will not register invalid step at `{k}`: already confirmed at `{prev_k}`"
  else return {data with stepInvalidUpTo := k}

private def next (info : Info State) (nextState : State.TermsAt k.succ)
: Unknown.Data State k → Smt (Unknown.Data State k.succ)
| ⟨posActlit, currNegActlit, currPred, baseValid, stepInvalid, stepValid⟩ => do
  -- ~~sanity~~ deactivated for now to allow BMC/pure-step independent checkers
  -- if ¬ baseValid then
  --   Error.throwUser s!"cannot produce next unknown data, candidate base validity unconfirmed"
  -- turn current negative actlit off
  currNegActlit.deactivate
  -- activate predicate at `k`
  posActlit.activate currPred
  -- activate predicate negation at `k + 1`
  let nextPred ← info.pred nextState
  let nextNegActlit ← Actlit.fresh
  nextNegActlit.activate (← nextPred.not)
  -- done
  return ⟨posActlit, nextNegActlit, nextPred, baseValid, stepInvalid, stepValid⟩

end Unknown.Data

abbrev Unknown (State : Symbols S) := Status State (Unknown.Data State)

namespace Unknown

protected def toString (unk : Unknown State depth) : String := toString unk

def next (nextState : State.TermsAt k)
: Unknown State k → Smt (Unknown State k.succ)
| .init info =>
  return .mk info (← Unknown.Data.init info nextState)
| .mk info data =>
  return .mk info (← data.next info nextState)

def isBaseValid {k : Nat} (unk : Unknown State k.succ) : Bool :=
  unk.data.isBaseValid

def isStepInvalid {k : Nat} (unk : Unknown State k.succ) : Bool :=
  unk.data.isStepInvalid

def isInvariant? {k : Nat} (unk : Unknown State k.succ) : Option Nat :=
  unk.data.isInvariant?

def toInvariant? {k : Nat} (unk : Unknown State k.succ) : Option (Invariant State k.succ) :=
  return .mk unk.info (← unk.data.toInvariant?)

def checkFalsified {k : Nat} (unk : Unknown State k.succ) : Smt.Sat Bool :=
  Bool.not <$> Smt.getVal unk.data.currPred

def confirmBase {k : Nat} (unk : Unknown State k.succ) : Res (Unknown State k.succ) :=
  return unk.updateData (← unk.data.confirmBase)

def confirmStep {k : Nat} (unk : Unknown State k.succ.succ) : Res (Unknown State k.succ.succ) :=
  return unk.updateData (← unk.data.confirmStep)

def invalidStep {k : Nat} (unk : Unknown State k.succ.succ) : Res (Unknown State k.succ.succ) :=
  return unk.updateData (← unk.data.invalidStep)

end Unknown

def mkUnknown (name : String) (pred : State.StatePredicate) : Unknown State 0 :=
  .init ⟨name, pred⟩

end Candidate



inductive Candidate (State : Symbols S) (k : Nat)
| unknown : Candidate.Unknown State k → Candidate State k
| invariant : Candidate.Invariant State k → Candidate State k
| falsified : Candidate.Falsified State k → Candidate State k

namespace Candidate

def map
  (ifUnknown : Unknown State k → α)
  (ifInvariant : Invariant State k → α)
  (ifFalsified : Falsified State k → α)
: Candidate State k → α
| .unknown status => ifUnknown status
| .invariant status => ifInvariant status
| .falsified status => ifFalsified status

section variable (candidate : Candidate State k)

def info : Info State :=
  candidate.map Status.info Status.info Status.info
def name (c : Candidate State k) : String := c.info.name
def pred (c : Candidate State k) : State.StatePredicate := c.info.pred

def unknown? : Option (Unknown State k) := candidate.map some (𝕂 none) (𝕂 none)
def invariant? : Option (Invariant State k) := candidate.map (𝕂 none) some (𝕂 none)
def falsified? : Option (Falsified State k) := candidate.map (𝕂 none) (𝕂 none) some

def isUnknown := candidate.unknown?.isSome
def isInvariant := candidate.invariant?.isSome
def isFalsified := candidate.falsified?.isSome

end

abbrev Map (α : Type) := RBMap String α

namespace Map

def valsToLines [ToString α] (map : Map α) (desc : String) (pref := "") : Array String := Id.run do
  if map.isEmpty then
    return #[pref ++ "no " ++ desc]
  let mut res := Array.mkEmpty <| map.size + 2
  res := res.push <| pref ++ desc ++ ": {}"
  for (_, val) in map do
    res := res.push s!"{pref}  {val}"
  res := res.push <| pref ++ "}"
  res

end Map

abbrev UnknownMap (State : Symbols S) depth := Map (Unknown State depth)

namespace UnknownMap

def toLines (unk : UnknownMap State depth) (pref := "") : Array String :=
  unk.valsToLines "unknown" pref

def addBaseActivators {k : Nat} (unk : UnknownMap State k.succ) (activators : Array Formula)
: Term.Build (Array Formula) := do
  let mut currNegActlits := #[]
  let mut activators := activators
  for (_, unk) in unk do
    if ¬ unk.isBaseValid then
      currNegActlits := currNegActlits.push unk.data.currNegActlit
  if h : 2 ≤ activators.size then
    return activators.push (← Term.mkOr activators h)
  else if h : 0 < activators.size then
    return activators.push activators[0]
  else Error.throwUser "expected at least one unknown candidate, got none"

def addStepActivators {k : Nat} (unk : UnknownMap State k.succ) (activators : Array Formula)
: Term.Build (Array Formula) := do
  let mut currNegActlits := #[]
  let mut activators := activators
  for (_, unk) in unk do
    if unk.isStepInvalid then
      activators := activators.push unk.data.posActlit
      currNegActlits := currNegActlits.push unk.data.currNegActlit
  if h : 2 ≤ activators.size then
    return activators.push (← Term.mkOr activators h)
  else if h : 0 < activators.size then
    return activators.push activators[0]
  else Error.throwUser "expected at least one unknown candidate, got none"

def isNextBaseReady {k : Nat} (unk : UnknownMap State k.succ) : Bool :=
  ¬ unk.isEmpty ∧ unk.all fun _ unk => unk.isBaseValid

def isNextStepReady {k : Nat} (unk : UnknownMap State k.succ) : Bool :=
  k = 0 ∨ (¬ unk.isEmpty ∧ unk.all fun _ unk => unk.isStepInvalid)

end UnknownMap

abbrev InvariantMap (State : Symbols S) depth := Map (Invariant State depth)

namespace InvariantMap

def toLines (inv : InvariantMap State depth) (pref := "") : Array String :=
  inv.valsToLines "invariant" pref

def addActivators {k : Nat} (inv : InvariantMap State k.succ)
: (activators : Array Formula) → Array Formula :=
  inv.foldl fun activators _ inv =>
    activators.push inv.data.posActlit

end InvariantMap

abbrev FalsifiedMap (State : Symbols S) depth := Map (Falsified State depth)

namespace FalsifiedMap

def toLines (fls : FalsifiedMap State depth) (pref := "") : Array String :=
  fls.valsToLines "falsified" pref

end FalsifiedMap

end Candidate



inductive Candidates (State : Symbols S) : (depth : Nat) → Type
| init
  (candidates : Candidate.UnknownMap State 0 := .empty)
: Candidates State 0
| mk {k : Nat}
  (unknown : Candidate.UnknownMap State k.succ)
  (invariant : Candidate.InvariantMap State k.succ)
  (falsified : Candidate.FalsifiedMap State k.succ)
: Candidates State k.succ

namespace Candidates

open Candidate (Map)
export Candidate (Unknown Invariant Falsified UnknownMap InvariantMap FalsifiedMap Info)

def empty : Candidates State 0 := .init .empty

def toLines (pref := "") : Candidates State depth → Array String
| .init unk =>
  let array := #[pref ++ "candidates at 0 {"] ++ unk.toLines (pref ++ "  ")
  array.push <| pref ++ "}"
| .mk unk inv fls  =>
  let array := #[pref ++ "candidates at 0 {"]
    ++ unk.toLines (pref ++ "  ")
    ++ inv.toLines (pref ++ "  ")
    ++ fls.toLines (pref ++ "  ")
  array.push <| pref ++ "}"


def unknown : Candidates State depth → UnknownMap State depth
| .init unk | .mk unk .. => unk

def isDone (cs : Candidates State depth) : Bool :=
  cs.unknown.isEmpty


def isNextBaseReady : (self : Candidates State depth) → Bool
| .init unk => true
| .mk unk .. => unk.isNextBaseReady

def isNextStepReady : (self : Candidates State depth) → Bool
| .init unk => true
| .mk unk .. => unk.isNextBaseReady

def invariant {depth : Nat} : Candidates State depth.succ → InvariantMap State depth.succ
| .mk _ inv _ => inv

def falsified {depth : Nat} : Candidates State depth.succ → FalsifiedMap State depth.succ
| .mk _ _ fls => fls

private def setUnknown {k : Nat} (newUnk : UnknownMap State k.succ)
: Candidates State k.succ → Candidates State k.succ
| .mk _ inv fls => .mk newUnk inv fls

def insertFalsified {k : Nat}
  (newFls : Candidate.Falsified State k.succ)
: Candidates State k.succ → Res (Candidates State k.succ)
| .mk unk inv fls => do
  let (prev?, fls) := fls.insert' newFls.name newFls
  if prev?.isSome then
    s!"cannot register `{newFls.name}` as falsified, \
    a candidate with this name is already registered as such"
    |> Error.throwUser
  return .mk unk inv fls

def insertInvariant {k : Nat}
  (newInv : Candidate.Invariant State k.succ)
: Candidates State k.succ → Res (Candidates State k.succ)
| .mk unk inv fls => do
  let (prev?, inv) := inv.insert' newInv.name newInv
  if prev?.isSome then
    s!"cannot register `{newInv.name}` as invariant, \
    a candidate with this name is already registered as such"
    |> Error.throwUser
  return .mk unk inv fls

def insertUnknown
  (newUnk : Candidate.Unknown State depth)
: Candidates State depth → Res (Candidates State depth)
| .init unk => do
  let (prev?, unk) := unk.insert' newUnk.info.name newUnk
  if prev?.isSome then
    s!"cannot register `{newUnk.info.name}` as unknown, \
    a candidate with this name is already registered as such"
    |> Error.throwUser
  return .init unk
| cs@(.mk unk inv fls) => do
  if let some newInv := newUnk.toInvariant?
  then cs.insertInvariant newInv else
    let (prev?, unk) := unk.insert' newUnk.info.name newUnk
    if prev?.isSome then
      s!"cannot register `{newUnk.info.name}` as unknown, \
      a candidate with this name is already registered as such"
      |> Error.throwUser
    return .mk unk inv fls

instance : ForIn m (Candidates State depth) (Candidate State depth) where
  forIn
  | .init unk, acc, f =>
    forIn unk acc fun (_, c) => f (.unknown c)
  | .mk unk inv fls, acc, f => do
    let mut acc := acc
    for (_, c) in unk do
      match ← f (.unknown c) acc with
      | .yield acc' => acc := acc'
      | .done acc' => return acc'
    for (_, c) in inv do
      match ← f (.invariant c) acc with
      | .yield acc' => acc := acc'
      | .done acc' => return acc'
    for (_, c) in fls do
      match ← f (.falsified c) acc with
      | .yield acc' => acc := acc'
      | .done acc' => return acc'
    return acc

def isEmpty : Candidates State depth → Bool
| .init unk => unk.isEmpty
| .mk unk inv fls => unk.isEmpty ∧ inv.isEmpty ∧ fls.isEmpty

section variable {depth : Nat} (cs : Candidates State depth.succ)

def unknownCount := cs.unknown.size
def invariantCount := cs.invariant.size
def falsifiedCount := cs.falsified.size

def addBaseActivators : Array Formula → Term.Build (Array Formula) :=
  cs.unknown.addBaseActivators

def addStepActivators : Array Formula → Term.Build (Array Formula) :=
  cs.unknown.addStepActivators ∘ cs.invariant.addActivators

end

def next (state : State.TermsAt k)
: (candidates : Candidates State k)
→ (h : ¬ candidates.isDone := by assumption)
→ Smt (Candidates State k.succ)
| .init unk, _ => do
  let unk ← unk.mapOnlyValM fun u => u.next state
  return .mk unk .empty .empty
| .mk unk inv fls, _ => do
  -- refuse unrolling if any `u ∈ unk` is *s.t.* `¬ u.isBaseValid ∧ ¬ u.isStepInvalid`
  let badCount := 0 |> unk.foldl fun badCount _ unk =>
    if unk.isBaseValid ∨ (0 < k ∧ unk.isStepInvalid) then badCount else badCount + 1
  if 0 < badCount then
    let baseStep := if k = 0 then "base" else "either base or step"
    if badCount = unk.size then
      Error.throwUser
        s!"will not unroll: unknown candidates have not been checked in {baseStep} at {k}"
    else for (_, unk) in unk do
      if ¬ unk.isBaseValid ∧ ¬ unk.isStepInvalid then
        let also := if let badCount + 1 := badCount then s!"and {badCount} other(s) have" else "has"
        Error.throwUser
          s!"will not unroll: candidate `{unk.name}` {also} not been checked in {baseStep} at {k}"
  let unk ← unk.mapOnlyValM fun u => u.next state
  let inv ← inv.mapOnlyValM fun i => i.next state
  let fls ← fls.mapOnlyValM fun f => f.next state
  return .mk unk inv fls

section variable {k : Nat} (self : Candidates State k.succ)

def registerBaseCex (cex : State.ValTrace k.succ) : Smt.Sat (Candidates State k.succ) := do
  let (self, unk) ← self.unknown.filterMapFoldM self
    fun self _ (unk : Unknown State _) => do
      if ¬ unk.isBaseValid ∧ (← unk.checkFalsified) then
        let self ← self.insertFalsified (.mk unk.info ⟨unk.data.currNegActlit, k, cex⟩)
        return (self, none)
      else return (self, some unk)
  return self.setUnknown unk

def registerBaseUnsat : Smt.Unsat (Candidates State k.succ) := do
  if self.unknown.isEmpty then return self else
    let (self, unk) ← self.unknown.filterMapFoldM self
      fun self _ (unk : Unknown State _) => do
        let unk ← unk.confirmBase
        if let some inv := unk.toInvariant? then
          let self ← self.insertInvariant inv
          pure (self, none)
        else pure (self, some unk)
    return self.setUnknown unk

def registerStepCex {k : Nat} (self : Candidates State k.succ.succ)
: Smt.Sat (Candidates State k.succ.succ) := do
  let unk ← self.unknown.mapOnlyValM fun (unk : Unknown State k.succ.succ) => do
    if ¬ unk.isStepInvalid ∧ (← unk.checkFalsified)
    then unk.invalidStep else pure unk
  return self.setUnknown unk

def registerStepUnsat {k : Nat} (self : Candidates State k.succ.succ)
: Smt.Unsat (Candidates State k.succ.succ) := do
  let (self, unk) ← self.unknown.filterMapFoldM self fun self _ unk => do
    if ¬ unk.isStepInvalid then
      let unk ← unk.invalidStep
      if let some inv := unk.toInvariant? then
        let self ← self.insertInvariant inv
        pure (self, none)
      else pure (self, some unk)
    else pure (self, some unk)
  return self.setUnknown unk

end

end Candidates



namespace Candidate.Unknown



end Candidate.Unknown
