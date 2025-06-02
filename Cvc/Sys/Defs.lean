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
  pred : {k : Nat} → State.PredAt k
  currentNegPred : Formula
  currentNegActlit : Actlit
  posActlit : Actlit
  status : State.Status

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
