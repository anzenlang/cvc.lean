/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Sys.Trace



namespace Cvc

namespace Symbols



structure Unroller (State : Symbols Struct) (depth : Nat) where
private mk' ::
  init : State.StatePred
  step : State.StateRel
  trace : State.TermTrace (depth + 1)

namespace Unroller

def mk [State : Symbols Struct]
  (init : State.StatePred) (step : State.StateRel)
: Smt (State.Unroller 0) :=
  return ⟨init, step, Trace.mkOne (← State.idents.declareAt 0)⟩

def idents [State : Symbols Struct] : (unroller : Unroller State k) → State.Idents :=
  fun _ => State.idents

section var_sys variable (sys : Unroller State k)

abbrev length := let _ := sys ; k + 1

abbrev CexTrace := State.ValTrace sys.length

abbrev Idx := Fin sys.length

abbrev idx0 : sys.Idx := ⟨0, by simp only [length, Nat.zero_lt_succ]⟩

abbrev idxLast : sys.Idx := ⟨k, by simp only [length, Nat.lt_add_one]⟩

def getTermsAt (i : sys.Idx) : State.TermsAt i := sys.trace.get i

def getTerms0 := sys.getTermsAt sys.idx0

def getTermsLast := sys.getTermsAt sys.idxLast

def unroll : Smt (State.TermsAt sys.length × State.Unroller k.succ) := do
  let terms' := sys.getTermsLast
  let terms ← State.idents.declareAt sys.length
  sys.step terms' terms >>= Smt.assert
  let trace := sys.trace.cons terms
  return ⟨terms, {sys with trace}⟩

def checkSatAnd [Monad m] (init : Bool)
  (assuming : Array Formula := #[])
  (ifSat : Smt.SatT m α := Smt.Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Smt.Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Smt.Unknown.unexpected)
: SmtT m α := do
  let mut assuming := assuming
  if init then
    let init ← sys.init sys.getTermsLast
    assuming := assuming.push init
  Smt.checkSatAnd assuming ifSat ifUnsat ifUnknown

def extractCexTrace : Smt.Sat sys.CexTrace := do
  sys.trace.mapM fun _ terms => terms.getVals

def findCexTrace? (init : Bool) (assuming : Array Formula := #[]) : Smt (Option sys.CexTrace) :=
  sys.checkSatAnd init assuming
    (ifSat := some <$> sys.extractCexTrace)
    (ifUnsat := pure none)

end var_sys

end Unroller
