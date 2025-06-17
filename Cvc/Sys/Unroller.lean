/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Sys.Trace



namespace Cvc

namespace Symbols



/-- Unroller for a trace of `length` states. -/
structure Unroller (State : Symbols Struct) (length : Nat) where
private mk' ::
  /-- State identifiers. -/
  idents : State.Idents
  /-- Init predicate. -/
  init : State.StatePred
  /-- Step predicate. -/
  step : State.StateRel
  /-- Trace of symbol-terms. -/
  trace : State.TermTrace length

namespace Unroller

/-- Constructs an unroller for `0` states. -/
def mk [State : Symbols Struct]
  (idents : State.Idents) (init : State.StatePred) (step : State.StateRel)
: State.Unroller 0 :=
  ⟨idents, init, step, .empty⟩

/-- Number of states in an unroller's trace. -/
protected abbrev length : Unroller State length → Nat := 𝕂 length

/-- Type of legal state indices in an unroller. -/
abbrev Idx : Unroller State length → Type := 𝕂 <| Fin length

section var_sys variable (sys : Unroller State length)

/-- Alias for a trace of symbol-values. -/
abbrev CexTrace := State.ValueTrace sys.length

/-- Retrieves the symbol-terms at some index. -/
def getTermsAt (i : sys.Idx) : State.TermsAt i := sys.trace.get i

/-- Extracts a trace of state-values in a *sat* context. -/
def extractCex : Smt.Sat sys.CexTrace := do
  sys.trace.mapM fun _ terms => terms.getValues



section var_k_succ variable {k : Nat} (sys : Unroller State k.succ)

/-- Index `0` as a legal index for a non-empty unroller. -/
abbrev idx0: sys.Idx := ⟨0, by simp only [Nat.zero_lt_succ]⟩

/-- Last index of a non-empty unroller. -/
abbrev idxLast : sys.Idx := ⟨k, by simp only [Nat.lt_add_one]⟩

/-- Retrieves the symbol-terms at index 0 in a non-empty unroller. -/
abbrev getTerms0 : State.TermsAt 0 := sys.getTermsAt sys.idx0

/-- Retrieves the symbol-terms at the highest index in a non-empty unroller. -/
abbrev getTermsLast : State.TermsAt k := sys.getTermsAt sys.idxLast

/-- Asserts a transition between the current latest state and the next latest state. -/
private def assertNextStep (next : State.TermsAt k.succ) : Smt Unit :=
  sys.step sys.getTermsLast next >>= Smt.assert

section variable [Monad m] (init : Bool)
  (assuming : Array Formula := #[])
  (ifSat : Smt.SatT m α := Smt.Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Smt.Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Smt.Unknown.unexpected)

/-- `Smt.checkSatAnd` with the `init` flag (de)activating that state `0` is initial. -/
def checkSatAnd : SmtT m α := do
  let assuming ←
    if init then assuming.push <$> sys.init sys.getTerms0 else pure assuming
  Smt.checkSatAnd assuming ifSat ifUnsat ifUnknown

/-- Performs a *base* check, *i.e.* state `0` is initial. -/
def checkSatBaseAnd : SmtT m α := sys.checkSatAnd (init := true) assuming ifSat ifUnsat ifUnknown
/-- Performs a *step* check, *i.e.* state `0` is not initial. -/
def checkSatStepAnd : SmtT m α := sys.checkSatAnd (init := false) assuming ifSat ifUnsat ifUnknown

end

/-- Performs a `Unroller.checkSatAnd` and extracts a cex trace if sat.

- `init`: controls whether state `0` must be an initial state.
-/
def findCex? (init : Bool) (assuming : Array Formula := #[]) : Smt (Option sys.CexTrace) :=
  sys.checkSatAnd init assuming
    (ifSat := some <$> sys.extractCex)
    (ifUnsat := pure none)

end var_k_succ



/-- Declares the next state. -/
private def declareNext : Smt (State.TermsAt length) :=
  let _ := sys ; sys.idents.declareAt length

/-- Unrolls one state further. -/
def unroll : Smt (State.TermsAt length × State.Unroller length.succ) := do
  let next ← sys.declareNext
  let trace := sys.trace.cons next
  let res := Prod.mk next {sys with trace}
  by cases length with
  | succ _ => exact do sys.assertNextStep next ; return res
  | zero => exact return res

@[inherit_doc unroll]
def unroll' : Smt (State.Unroller length.succ) :=
  Prod.snd <$> sys.unroll

end var_sys

end Unroller
