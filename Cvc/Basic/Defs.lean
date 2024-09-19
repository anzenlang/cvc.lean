/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init



/-! # Basic definitions -/
namespace Cvc



export cvc5 (Kind)

/-- Type for cvc5 terms. -/
structure Term where
ofCvc5 ::
  toCvc5 : cvc5.Term

instance : Inhabited Term where
  default := Term.ofCvc5 cvc5.Term.instInhabited.default

instance : Ord Term where
  compare t t' :=
    compare t.toCvc5.getId t'.toCvc5.getId

/-- Type for cvc5 sorts. -/
structure Srt where
ofCvc5 ::
  toCvc5 : cvc5.Sort

instance : Inhabited Srt where
  default := Srt.ofCvc5 cvc5.Sort.instInhabited.default

-- @[inherit_doc cvc5.Proof]
abbrev Proof := cvc5.Proof

@[inherit_doc cvc5.ProofRule]
abbrev Proof.Rule := cvc5.ProofRule

@[inherit_doc cvc5.ProofRewriteRule]
abbrev Proof.RewriteRule := cvc5.ProofRewriteRule



/-! ## Proofs -/
namespace Proof

export cvc5.Proof (
  beq
  getArguments getChildren getResult getRewriteRule getRule
  hash null
)

end Proof



/-! ## Term Manager -/
namespace Term

/-- Cvc5 term manager. -/
def Manager : Type := ULift cvc5.TermManager

namespace Manager
def mk : BaseIO Manager := do
  let tm ← cvc5.TermManager.new
  return ULift.up tm

def ofCvc5 : cvc5.TermManager → Manager := ULift.up

def toCvc5 : Manager → cvc5.TermManager := ULift.down
end Manager

/-- `Manager` error/state-monad transformer. -/
abbrev ManagerT (m : Type → Type) :=
  ExceptT Error (StateT Manager m)

/-- `Manager` error/state-monad wrapped in `IO`. -/
abbrev ManagerIO :=
  ManagerT IO

abbrev ManagerM : Type → Type :=
  ManagerT Id

instance [Monad m] : MonadLift (ManagerM) (ManagerT m) where
  monadLift code tm := do
    let (res, tm) := code tm
    return (res, tm)

instance [Monad m] : MonadExcept Error (ManagerT m) where
  throw e tm := return (.error e, tm)
  tryCatch code errorDo tm := do
    match ← code tm with
    | (.ok a, tm) => return (.ok a, tm)
    | (.error e, tm) => errorDo e tm

instance : MonadLift (Except cvc5.Error) (ManagerM) where
  monadLift
  | .ok res => return res
  | .error e => throw (Error.ofCvc5 e)

end Term



/-! ## `Smt`: a term manager and a solver -/

/-- Smt state.

Aggregates a `Term.Manager` and a `cvc5.Solver`.
-/
structure Smt : Type where
private mkRaw ::
  private termManager : Term.Manager
  private solver : cvc5.Solver

/-- `Smt` error/state-monad transformer. -/
abbrev SmtT (m : Type → Type u) := ExceptT Error (StateT Smt m)

/-- Plain smt error/state-monad. -/
abbrev SmtM := SmtT Id

/-- `Smt` error/state-monad wrapped in `IO`. -/
abbrev SmtIO := SmtT IO

namespace SmtT
def throwInternal [Monad m] (msg : String) : SmtT m α :=
  .internal msg |> throw

def throwUser [Monad m] (msg : String) : SmtT m α :=
  .userError msg |> throw

instance instMonadLiftSmtM [Monad m] : MonadLift SmtM (SmtT m) where
  monadLift code smt := do
    let (res, solver) := code smt
    return (res, solver)

instance instMonadLiftManagerT [Monad m] : MonadLift (Term.ManagerT m) (SmtT m) where
  monadLift code smt := do
    let (res, termManager) ← code smt.termManager
    return (res, {smt with termManager})

instance instMonadExcept [Monad m] : MonadExcept Error (Term.ManagerT m) where
  throw e smt := return (.error e, smt)
  tryCatch code errorDo smt := do
    match ← code smt with
    | (.ok res, smt) => return (.ok res, smt)
    | (.error e, smt) => errorDo e smt
end SmtT




/-! ## Sort/term conversion classes  -/

/-- Can be seen as a `Srt`. -/
class ToSrt (α : Type) where
  /-- Produces an `Srt` corresponding to `α`. -/
  srt : Term.ManagerM Srt

/-- Can be encoded as a `Term`. -/
class ToTerm (α : Type) extends ToSrt α where
  /-- Produces a `Term` corresponding to some `α`-value. -/
  toTerm : α → Term.ManagerM Term

/-- Can transform a `Term` into a native value. -/
class ValueOfTerm (α : Type) where
  valueOfTerm : Term → Term.ManagerM α



/-! ## Smt and smt transformer -/

namespace SmtT

variable [Monad m]



instance instMonadLiftCvc5 : MonadLift (cvc5.SolverT m) (SmtT m) where
  monadLift code smt := do
    let (res, solver) ← code smt.solver
    return (res.mapError Error.ofCvc5, {smt with solver})



/-! ## Runners -/

/-- Runs `SmtT` code given a term manager. -/
def runWith (tm : Term.Manager) (code : SmtT m α) : m (Except Error α) := do
  let res ←
    cvc5.Solver.run tm.down fun solver => do
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
