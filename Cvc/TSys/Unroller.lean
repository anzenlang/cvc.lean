/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.TSys.Unrolling



namespace Cvc.Safe



namespace Symbols

structure UFrame (State : Symbols S) (k : Nat) : Type where
  state : State.TermsAt k

structure Unroller (State : Symbols S) where
private mkRaw ::
  logic : Logic
  symbols : State.Idents
  init : State.Predicate
  step : State.Relation
  depth : Nat
  unrolling : State.Unrolling State.UFrame (depth + 1)

namespace Unroller

def mk [Monad m] [State : Symbols S]
  (logic : Logic) (symbols : State.Idents)
  (init : State.Predicate) (step : State.Relation)
: SmtT m (Unroller State) := do
  Smt.setOption .produceModels
  Smt.setLogic logic
  let svars0 ← symbols.declareAt 0
  return {
    logic, symbols
    init, step
    depth := 0,
    unrolling := Symbols.Unrolling.empty.cons ⟨svars0⟩
  }

variable (sys : Unroller State)

abbrev CexTrace :=
  State.Unrolling State.Model (sys.depth + 1)

def getUFrameAt (i : Fin sys.depth.succ) : State.UFrame i :=
  sys.unrolling.get i

def getSymbolsAt (i : Fin sys.depth.succ) :=
  sys.getUFrameAt i |>.state

abbrev currentOffset : Fin sys.depth.succ :=
  ⟨0, by simp only [Nat.succ_eq_add_one, Nat.zero_lt_succ]⟩

def getCurrentUFrame : State.UFrame 0 :=
  sys.getUFrameAt sys.currentOffset

def getCurrentSymbols :=
  sys.getCurrentUFrame |>.state

abbrev oldestOffset : Fin sys.depth.succ := ⟨
  sys.depth.succ.pred,
  by simp only [Nat.succ_eq_add_one, Nat.pred_eq_sub_one, Nat.add_one_sub_one, Nat.lt_add_one]
⟩

def getOldestUFrame : State.UFrame sys.oldestOffset :=
  sys.getUFrameAt sys.oldestOffset

def getOldestSymbols :=
  sys.getOldestUFrame |>.state

def unroll (sys : Unroller State) : Nat → SmtM (Unroller State)
| 0 => return sys
| n + 1 => do
  let svars' := sys.getOldestSymbols
  let svars ← sys.symbols.declareAt sys.depth.succ
  let step ← sys.step svars svars'
  Smt.assert step
  let unrolling := sys.unrolling.cons ⟨svars⟩
  let sys := { sys with
    unrolling
    depth := sys.depth + 1
  }
  sys.unroll n

def unrollOnce
  (sys : Unroller State)
: SmtM (State.TermsAt sys.depth.succ.succ × Unroller State) := do
  let sys ← sys.unroll 1
  return (sys.getOldestSymbols, sys)

def checkSat [Monad m] (inInit : Bool)
  (assuming : Array (Term Bool) := #[])
  (ifSat : Smt.SatT m α := Smt.Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Smt.Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Smt.Unknown.unexpected)
: SmtT m α := do
  -- add `init` at the last state index to `assuming` if asked to
  let mut assuming := assuming
  if inInit then
    let init ← sys.init sys.getOldestSymbols
    assuming := assuming.push init
  -- let's do this
  Smt.checkSat assuming ifSat ifUnsat ifUnknown

def extractCexTrace : Smt.SatM sys.CexTrace := do
  let trace ← sys.unrolling.mapM fun _ svars => do
    svars.state.getModel
  return trace.reverse

def findCexTrace? (inInit : Bool)
  (assuming : Array (Term Bool) := #[])
: SmtM (Option sys.CexTrace) :=
  sys.checkSat inInit assuming
    (ifSat := some <$> sys.extractCexTrace)
    (ifUnsat := pure none)

-- def preImage
--   (leadingTo : State.Predicate) (verifying : State.Predicate)
--   (n : Nat := 1)
--   (h : 0 < n := by first | simp | omega)
-- : SmtM (Term Bool) :=
--   sorry

end Unroller
