/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Sys.Trace



namespace Cvc

namespace Symbols



structure Unroller (State : Symbols Struct) (length : Nat) where
private mk' ::
  idents : State.Idents
  init : State.StatePred
  step : State.StateRel
  trace : State.TermTrace length

namespace Unroller

def mk [State : Symbols Struct]
  (idents : State.Idents) (init : State.StatePred) (step : State.StateRel)
: State.Unroller 0 :=
  ⟨idents, init, step, .empty⟩

section var_sys variable (sys : Unroller State length)

protected abbrev length : Nat := let _ := sys ; length

abbrev CexTrace := State.ValTrace sys.length

abbrev TermCexTrace := State.ValueTrace sys.length

abbrev Idx := let _ := sys ; Fin length

def getTermsAt (i : sys.Idx) : State.TermsAt i := sys.trace.get i

def extractCexTrace : Smt.Sat sys.CexTrace := do
  sys.trace.mapM fun _ terms => terms.getVals

def extractTermCexTrace : Smt.Sat sys.TermCexTrace := do
  sys.trace.mapM fun _ terms => terms.getValues



section var_k_succ variable {k : Nat} (sys : Unroller State k.succ)

abbrev idx0: sys.Idx := ⟨0, by simp only [Nat.zero_lt_succ]⟩

abbrev idxLast : sys.Idx := ⟨k, by simp only [Nat.lt_add_one]⟩

abbrev getTerms0 : State.TermsAt 0 := sys.getTermsAt sys.idx0

abbrev getTermsLast : State.TermsAt k := sys.getTermsAt sys.idxLast

private def assertNextStep (next : State.TermsAt k.succ) : Smt Unit :=
  sys.step sys.getTermsLast next >>= Smt.assert

section variable [Monad m] (init : Bool)
  (assuming : Array Formula := #[])
  (ifSat : Smt.SatT m α := Smt.Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Smt.Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Smt.Unknown.unexpected)

def checkSatAnd : SmtT m α := do
  let assuming ←
    if init then assuming.push <$> sys.init sys.getTerms0 else pure assuming
  Smt.checkSatAnd assuming ifSat ifUnsat ifUnknown

def checkSatBaseAnd : SmtT m α := sys.checkSatAnd (init := true) assuming ifSat ifUnsat ifUnknown
def checkSatStepAnd : SmtT m α := sys.checkSatAnd (init := false) assuming ifSat ifUnsat ifUnknown

end

def findCexTrace? (init : Bool) (assuming : Array Formula := #[]) : Smt (Option sys.CexTrace) :=
  sys.checkSatAnd init assuming
    (ifSat := some <$> sys.extractCexTrace)
    (ifUnsat := pure none)

def findTermCexTrace? (init : Bool)
  (assuming : Array Formula := #[])
: Smt (Option sys.TermCexTrace) :=
  sys.checkSatAnd init assuming
    (ifSat := some <$> sys.extractTermCexTrace)
    (ifUnsat := pure none)

end var_k_succ



private def declareNext : Smt (State.TermsAt length) :=
  let _ := sys ; sys.idents.declareAt length

def unroll : Smt (State.TermsAt length × State.Unroller length.succ) := do
  let next ← sys.declareNext
  let trace := sys.trace.cons next
  let res := Prod.mk next {sys with trace}
  by cases length with
  | succ _ => exact do sys.assertNextStep next ; return res
  | zero => exact return res

def unroll' : Smt (State.Unroller length.succ) :=
  Prod.snd <$> sys.unroll

end var_sys

end Unroller
