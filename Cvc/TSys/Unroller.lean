import Cvc.TSys.Unrolling



namespace Cvc.Safe.TSys



structure SVars.UFrame (State : SVars S) (k : Nat) : Type where
  state : State.Terms k



structure Unroller (State : SVars S) where
private mkRaw ::
  logic : Logic
  symbols : State.Symbols
  init : State.Predicate
  step : State.Relation
  depthSucc : Nat
  unrolling : State.Unrolling State.UFrame depthSucc
  zero_lt_depthSucc : 0 < depthSucc := by omega

abbrev SVars.Unroller (State : SVars S) :=
  TSys.Unroller State

namespace Unroller

def mk [Monad m] [State : SVars S]
  (logic : Logic) (symbols : State.Symbols)
  (init : State.Predicate) (step : State.Relation)
: SmtT m (Unroller State) := do
  Smt.setOption .produceModels
  Smt.setLogic logic
  let svars0 ← symbols.declare 0
  return {
    logic, symbols
    init, step
    depthSucc := 1,
    unrolling := SVars.Unrolling.empty.cons ⟨svars0⟩
  }

def depth : Unroller State → Nat
| { depthSucc := depth + 1, .. } => depth

variable (sys : Unroller State)

abbrev CexTrace :=
  State.Unrolling State.Model sys.depthSucc

@[simp]
theorem inv_depthSucc : 0 < sys.depthSucc := sys.zero_lt_depthSucc

def getUFrameAt (i : Fin sys.depthSucc) : State.UFrame i :=
  sys.unrolling.get i

def getSVarsAt (i : Fin sys.depthSucc) :=
  sys.getUFrameAt i |>.state

abbrev currentOffset : Fin sys.depthSucc :=
  ⟨0, sys.inv_depthSucc⟩

def getCurrentUFrame : State.UFrame 0 :=
  sys.getUFrameAt sys.currentOffset

def getCurrentSVars :=
  sys.getCurrentUFrame |>.state

abbrev oldestOffset : Fin sys.depthSucc :=
  ⟨sys.depthSucc.pred, Nat.pred_lt_of_lt sys.inv_depthSucc⟩

def getOldestUFrame : State.UFrame sys.oldestOffset :=
  sys.getUFrameAt sys.oldestOffset

def getOldestSVars :=
  sys.getOldestUFrame |>.state

def unroll (sys : Unroller State) : Nat → SmtM (Unroller State)
| 0 => return sys
| n + 1 => do
  let svars' := sys.getOldestSVars
  let svars ← sys.symbols.declare sys.depthSucc
  let step ← sys.step svars svars'
  Smt.assert step
  let unrolling := sys.unrolling.cons ⟨svars⟩
  let sys := { sys with
    unrolling
    depthSucc := sys.depthSucc + 1
    zero_lt_depthSucc := Nat.zero_lt_succ sys.depthSucc
  }
  sys.unroll n

def unrollOnce (sys : Unroller State) : SmtM (State.Terms sys.depthSucc.succ × Unroller State) := do
  let sys ← sys.unroll 1
  return (sys.getOldestSVars, sys)

def checkSat [Monad m] (inInit : Bool)
  (assuming : Array (Term Bool) := #[])
  (ifSat : Smt.SatT m α := Smt.Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Smt.Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Smt.Unknown.unexpected)
: SmtT m α := do
  -- add `init` at the last state index to `assuming` if asked to
  let mut assuming := assuming
  if inInit then
    let init ← sys.init sys.getOldestSVars
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
