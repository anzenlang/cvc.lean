import CvcTest.Safe.Init



namespace Cvc.Safe.Test.Minimize



abbrev Decl (_ : Type u) := String

abbrev Var (F : Type → Type) := F Int

namespace Var

protected abbrev Decl := Var Decl
protected abbrev Term := Var Term
protected abbrev Val := Var Id

end Var

class Vars (S : (Type → Type) → Type) where
  mapM {F G : Type → Type} [Monad m] (self : S F) (f : Var F → m (Var G)) : m (S G)

namespace Vars
variable [I : Vars S]

def declare (terms : S Decl) : SmtM (S Term) := do
  I.mapM terms (Smt.declareFun · Int)

def getModel (terms : S Term) : Smt.SatM (S Id) := do
  I.mapM terms Smt.getValue
end Vars

abbrev Fun (S : (Type → Type) → Type) (α : Type) := S Term → Term.ManagerM (Term α)

abbrev Pred S := Fun S Bool



structure Arith (S : (Type → Type) → Type) extends Vars S where
mkRaw::
  vars : S Decl
  constraints : Array (Pred S)

namespace Arith
def mk [Vars S] (vars : S Decl) (constraints : Array (Pred S)) : Arith S :=
  mkRaw inferInstance vars constraints

variable (self : Arith S)

open Smt in
def findModel? [Monad m]
  (ifSat : S Term → S Id → Smt.SatT m α)
: SmtT m (Option α) := do
  setLogic Logic.qf_lia
  setOption "produce-models" "true"

  let varTerms ← self.declare self.vars

  for constraint in self.constraints do
    let pred ← constraint varTerms -- `Term Bool`
    assert pred

  checkSat
    (ifSat := do
      let model ← self.getModel varTerms
      ifSat varTerms model)
    (ifUnsat := return none)

end Arith

def findModelWith? [Vars S] [Monad m]
  (vars : S Decl) (constraints : Array (Pred S))
  (ifSat : S Term → S Id → Smt.SatT m α)
: SmtT m (Option α) :=
  Arith.mk vars constraints |>.findModel? ifSat

def findModel? [Vars S] [Monad m]
  (vars : S Decl) (constraints : Array (Pred S))
: SmtT m (Option (S Id)) :=
  findModelWith? vars constraints fun _ model => return model



abbrev Minimized? (S : (Type → Type) → Type) := Option (Int × S Id)

partial def minimize
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  [Vars S] (vars : S Decl)
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
