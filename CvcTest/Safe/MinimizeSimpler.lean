/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Safe.Init



namespace Cvc.Safe.Test.Minimize



abbrev IntTerm := Term Int

/-- Instantiated by user-defined variable-list-like structures. -/
class Vars (V : Type → Type) where
  /-- Apply some monadic treatment to whatever `V` stores. -/
  mapM [Monad m] {α β : Type} (self : V α) (f : α → m β) : m (V β)

namespace Vars
variable [I : Vars V]

/-- Turns strings into declared (variable) `Term`s. -/
def declare (vars : V String) : SmtM (V IntTerm) := do
  I.mapM vars (Smt.declareFun · Int)

/-- Turns `Term`s into value, assuming a *satisfiable* context. -/
def getModel (terms : V IntTerm) : Smt.SatM (V Int) := do
  I.mapM terms Smt.getValue
end Vars

/-- Given custom variables as `Term`s, produces a `Term` of type `α`. -/
abbrev Fun (V : Type → Type) (α : Type) := V IntTerm → Term.ManagerM (Term α)

/-- Same as `Fun V Bool`. -/
abbrev Pred V := Fun V Bool




open Smt in
def findModelWith? [Monad m] [Vars V]
  (vars : V String)
  (constraints : Array (Pred V))
  (ifSat : V IntTerm → V Int → Smt.SatT m α)
: SmtT m (Option α) := do
  setLogic Logic.qf_lia
  setOption .produceModels

  let varTerms ← Vars.declare vars

  for constraint in constraints do
    let pred ← constraint varTerms -- `Term Bool`
    assert pred

  checkSat
    (ifSat := do
      let model ← Vars.getModel varTerms
      ifSat varTerms model)
    (ifUnsat := return none)

def findModel? [Monad m] [Vars V]
  (vars : V String) (constraints : Array (Pred V))
: SmtT m (Option (V Int)) :=
  findModelWith? vars constraints fun _ model => return model



/-- Minimization result: smallest value found and its corresponding model. -/
abbrev Minimized? (S : Type → Type) := Option (Int × S Int)

open scoped Term in
/-- Finds a minimum for `f(vars)` in the space delimited by `constraints`.

**NB**: without proper `constraints`, this function may not terminate.
-/
partial def minimize
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [Vars V]
  (vars : V String)
  (f : Fun V Int)
  (constraints : Array (Pred V) := #[])
  (res : Minimized? V := none)
  (count : Nat := 0)
: m (Minimized? V × Nat) := do
  let better? ←
    findModelWith? (m := m) vars constraints
      (fun terms model => do
        let f ← f terms
        let val ← Smt.getValue f
        return (val, model))
    |>.run
  match better? with
  | .ok (some (val, model)) =>
    let constraints := constraints.push
      fun terms => do
        let f ← f terms
        let val ← Term.mkInt val
        smt! f < val
    minimize vars f constraints (val, model) count.succ
  | .ok none => return (res, count)
  | .error e => IO.throwServerError s!"{e}"
