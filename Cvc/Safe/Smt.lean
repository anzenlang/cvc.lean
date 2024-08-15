/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe.Defs



/-! # Safe -/
namespace Cvc.Safe



namespace Smt



@[inherit_doc Cvc.Smt.setLogic]
def setLogic (logic : Logic) : SmtM Unit := do
  Cvc.Smt.setLogic logic

@[inherit_doc Cvc.Smt.assert]
def assert (formula : Term Bool) : SmtM Unit := do
  Cvc.Smt.assert formula.toUnsafe



@[inherit_doc Cvc.Smt.checkSat?]
def checkSat? : SmtM (Option Bool) := do
  Cvc.Smt.checkSat?



protected structure Sat where
private ofSmt ::
  private toSmt : Smt

protected abbrev SatT (m : Type → Type u) := ExceptT Error (StateT Smt.Sat m)

def Sat.unexpected [Monad m] : Smt.SatT m α :=
  .userError "unexpected sat result" |> throw

protected abbrev SatM := Smt.SatT Id

instance Sat.monadLiftSatM [Monad m] : MonadLift Smt.SatM (Smt.SatT m) where
  monadLift code sat :=
    return code sat



protected structure Unsat where
private ofSmt ::
  private toSmt : Smt

protected abbrev UnsatT (m : Type → Type u) := ExceptT Error (StateT Smt.Unsat m)

def Unsat.unexpected [Monad m] : Smt.UnsatT m α :=
  .userError "unexpected unsat result" |> throw

protected abbrev UnsatM := Smt.UnsatT Id

instance Unsat.monadLiftUnsatM [Monad m] : MonadLift Smt.UnsatM (Smt.UnsatT m) where
  monadLift code sat :=
    return code sat



protected structure Unknown where
private ofSmt ::
  private toSmt : Smt

protected abbrev UnknownT (m : Type → Type u) := ExceptT Error (StateT Smt.Unknown m)

def Unknown.unexpected [Monad m] : Smt.UnknownT m α :=
  .userError "could not decide (un)satisfiability" |> throw

protected abbrev UnknownM := Smt.UnknownT Id

instance Unknown.monadLiftUnknownM [Monad m] : MonadLift Smt.UnknownM (Smt.UnknownT m) where
  monadLift code sat :=
    return code sat



/-- Check satisfiability and run specific sat, unsat, or unknown code.

- `ifSat`: Runs when satisfiable, produces an unexpected-style error by default.
- `ifUnsat`: Runs when unsatisfiable, produces an unexpected-style error by default.
- `ifUnknown`: Runs when (un)satisfiability cannot be established, produces an unexpected-style
  error by default.
-/
def checkSat
  [Monad m]
  (ifSat : Smt.SatT m α := Smt.Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Smt.Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Smt.Unknown.unexpected)
: SmtT m α := fun smt => do
  match checkSat? smt with
  | (.ok (some true), smt) =>
    let (res, smt') ← ifSat ⟨smt⟩
    return (res, smt'.toSmt)
  | (.ok (some false), smt) =>
    let (res, smt') ← ifUnsat ⟨smt⟩
    return (res, smt'.toSmt)
  | (.ok none, smt) =>
    let (res, smt') ← ifUnknown ⟨smt⟩
    return (res, smt'.toSmt)
  | (.error e, smt) =>
    return (.error e, smt)

end Smt
