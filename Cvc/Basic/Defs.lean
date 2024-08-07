/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init



namespace Cvc



/-! ## Basic definitions -/



export cvc5 (Kind)

/-- Type for cvc5 terms. -/
def Term := cvc5.Term

/-- Type for cvc5 sorts. -/
def Srt := cvc5.Sort



/-! ### Term Manager -/
namespace Term

/-- Cvc5 term manager. -/
def Manager := cvc5.TermManager

def Manager.mk := cvc5.TermManager.new

/-- `Manager` error/state-monad transformer. -/
abbrev ManagerT (m : Type → Type u) :=
  ExceptT Error (StateT Manager m)

/-- `Manager` error/state-monad wrapped in `IO`. -/
abbrev ManagerIO :=
  ManagerT IO

end Term



/-! ### `Smt`: a term manager and a solver -/

/-- Smt state.

Aggregates a `Term.Manager` and a `cvc5.Solver`.
-/
structure Smt where
private mkRaw ::
  private termManager : cvc5.TermManager
  private solver : cvc5.Solver

/-- `Smt` error/state-monad transformer. -/
abbrev SmtT (m : Type → Type u) := ExceptT Error (StateT Smt m)

namespace SmtT
def throwInternal [Monad m] (msg : String) : SmtT m α :=
  .internal msg |> throw

def throwUser [Monad m] (msg : String) : SmtT m α :=
  .userError msg |> throw

instance instMonadLiftManagerT [Monad m] : MonadLift (Term.ManagerT m) (SmtT m) where
  monadLift code smt := do
    let (res, termManager) ← code smt.termManager
    return (res, {smt with termManager})
end SmtT

/-- `Smt` error/state-monad wrapped in `IO`. -/
abbrev SmtIO := SmtT IO




/-! ## Sort/term conversion classes  -/

/-- Can be seen as a `Srt`. -/
class ToSrt (α : Type u) where
  /-- Produces an `Srt` corresponding to `α`. -/
  srt [Monad m] : Term.ManagerT m Srt

/-- Can be encoded as a `Term`. -/
class ToTerm (α : Type u) extends ToSrt α where
  /-- Produces a `Term` corresponding to some `α`-value. -/
  toTerm [Monad m] : α → Term.ManagerT m Term



/-! ## Smt and smt transformer -/

namespace SmtT

variable [Monad m]



instance instMonadLiftCvc5 : MonadLift (cvc5.SolverT m) (SmtT m) where
  monadLift code smt := do
    let (res, solver) ← code smt.solver
    return (res.mapError Error.ofCvc5, {smt with solver})



/-! ### Runners -/

/-- Runs `SmtT` code given a term manager. -/
def runWith (tm : Term.Manager) (code : SmtT m α) : m (Except Error α) := do
  let res ←
    cvc5.Solver.run tm fun solver => do
      let (res, ⟨_, s⟩) ← code ⟨tm, solver⟩
      return (res.mapError Error.toCvc5, s)
  return res.mapError Error.ofCvc5

/-- Runs `SmtT` code, creates the term manager and the solver. -/
def run [MonadLiftT BaseIO m]
  (code : SmtT m α)
: ExceptT Error m α := do
  let tm ← Term.Manager.mk
  code.runWith tm

/-- Runs `SmtT` code, panics on errors by default. -/
def run! [MonadLiftT BaseIO m] [Inhabited α]
  (code : SmtT m α)
  (handleError : Error → m α := fun e => panic! s!"{e}")
: m α := do
  match ← run code with
  | .ok res => return res
  | .error e => handleError e

end SmtT

namespace Smt

@[inherit_doc SmtT.runWith]
protected def runWith := @SmtT.runWith

@[inherit_doc SmtT.run]
protected def run := @SmtT.run

@[inherit_doc SmtT.run]
protected def run! := @SmtT.run!

end Smt
