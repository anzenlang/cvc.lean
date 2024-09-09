import CvcTest.Safe.Init



namespace Cvc.Safe.Test.Minimize



abbrev ITerm := Term Int

/-- Instantiated by user-defined variable-list-like structures. -/
class Vars (S : Type → Type) where
  /-- Apply some monadic treatment to whatever `S` stores. -/
  mapM [Monad m] {α β : Type} (self : S α) (f : α → m β) : m (S β)

namespace Vars
variable [I : Vars S]

/-- Turns strings into declared (variable) `Term`s. -/
def declare (vars : S String) : SmtM (S ITerm) := do
  I.mapM vars (Smt.declareFun · Int)

/-- Turns `Term`s into value, assuming a *satisfiable* context. -/
def getModel (terms : S ITerm) : Smt.SatM (S Int) := do
  I.mapM terms Smt.getValue
end Vars

/-- Given custom variables as `Term`s, produces a `Term` of type `α`. -/
abbrev Fun (S : Type → Type) (α : Type) := S ITerm → Term.ManagerM (Term α)

/-- Same as `Fun S Bool`. -/
abbrev Pred S := Fun S Bool




open Smt in
def findModelWith? [Monad m] [Vars S]
  (vars : S String)
  (constraints : Array (Pred S))
  (ifSat : S ITerm → S Int → Smt.SatT m α)
: SmtT m (Option α) := do
  setLogic Logic.qf_lia
  setOption "produce-models" "true"

  let varTerms ← Vars.declare vars

  for constraint in constraints do
    let pred ← constraint varTerms -- `Term Bool`
    assert pred

  checkSat
    (ifSat := do
      let model ← Vars.getModel varTerms
      ifSat varTerms model)
    (ifUnsat := return none)

def findModel? [Monad m] [Vars S]
  (vars : S String) (constraints : Array (Pred S))
: SmtT m (Option (S Int)) :=
  findModelWith? vars constraints fun _ model => return model



/-- Minimization result: smallest value found and its corresponding model. -/
abbrev Minimized? (S : Type → Type) := Option (Int × S Int)

/-- Finds a minimum for `f(vars)` in the space delimited by `constraints`.

**NB**: without proper `constraints`, this function may not terminate.
-/
partial def minimize
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [Vars S]
  (vars : S String)
  (f : Fun S Int)
  (constraints : Array (Pred S) := #[])
  (res : Minimized? S := none)
  (count : Nat := 0)
: m (Minimized? S × Nat) := do
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
