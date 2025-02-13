/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Safe.Init



/-! # Minimizer for integer-valued functions over integers

Define and illustrate code that, given an int-valued function `f` with int-valued arguments, finds a
minimum for `f` over some domain specified by constraints over the arguments.
-/
namespace Cvc.Safe.Test.Minimize

open scoped Cvc.Safe.Term



/-! ## Boilerplate -/



namespace User
/-!
Users will have their own structure to represent variables, *i.e.* the function's arguments. Each
variable `v` has type `Int`, so for instance when constructing (typed) terms we want `v : Term Int`.

However users will first need to provide a way to declare variables; in this context, we'd like to
have a `v : String` (the name) so that we can declare it as a symbol of sort `Int`.

Also, we will produce *models* to give back to users; in this context, we want to give back a `v :
Int`.

So, depending on the context, the type of `v` (a field in the user's structure) changes. Hence users
define a polymorphic variable structures.
-/

structure MyVars (α : Type) where
  n1 : α
  n2 : α
  n3 : α

end User



/-!
To accept custom structures and work with them, we define a class `Vars` that asks users how to
apply a (monadic-)map-like operation on the variables.
-/

class Vars (V : Type → Type) where
  /-- Applies `f` to all variables in `vars` and reconstructs `V`'s structure. -/
  mapM [Monad m] (vars : V α) (f : α → m β) : m (V β)



namespace User
/-!
Users instantiate `Vars`, for most use-cases the process is straightforward and easily automated.
-/

instance : Vars MyVars where
  mapM vars f := do
    let n1 ← f vars.n1
    let n2 ← f vars.n2
    let n3 ← f vars.n3
    return MyVars.mk n1 n2 n3

end User



/-!
Alias to simplify notations a bit.
-/
abbrev IntTerm := Term Int



namespace Vars
/-!
Thanks to `Vars` we now know how to declare variables, or retrieve their values in a solver.

In what follows:
- `V String`: user's fields are `String`s, used for declarations;
- `V IntTerm`: user's fields are `Int`-`Term`s, for building terms and getting values;
- `V Int`: user's fields are `Int`-values, used for models.
-/

def declare [Vars V] (vars : V String) : SmtM (V IntTerm) :=
  Vars.mapM vars (Smt.declareFun · Int)

def getModel [Vars V] (vars : V IntTerm) : Smt.SatM (V Int) :=
  Vars.mapM vars Smt.getValue

end Vars



/-!
Here are a few convenient aliases.
-/

/-- Given custom variables as `Term Int`s, produces a `Term` of type `α`. -/
abbrev Fun (V : Type → Type) (α : Type) := V IntTerm → Term.ManagerM (Term α)

/-- Alias for `Fun V Bool`. -/
abbrev Pred V := Fun V Bool



/-! ## Model extraction

The next two functions produce a model, if any, for some constraints over some variables.
-/

open Smt in
/-- Given some variables and some constraints, find a model.

- `vars`: names for the user's variables;
- `constraints`: array of `Pred V = V IntTerm → Term.ManagerM (Term Bool)`
- `ifSat terms model`: continuation in the *satisfiable* case with
  - `terms : V IntTerm`: terms corresponding to each variable;
  - `model: V Int`: values for each variable in the model.
-/
def findModelAnd? [Monad m] [Vars V] [MonadLiftT IO m]
  (vars : V String)
  (constraints : Array (Pred V))
  (ifSat : V IntTerm → V Int → Smt.SatT m α)
: SmtT m (Option α) := do
  setLogic Logic.qf_lia -- SMT
  setOption .produceModels -- SMT

  let varTerms ← Vars.declare vars

  for constraint in constraints do
    let pred ← constraint varTerms -- `pred : Term Bool`
    assert pred -- SMT

  checkSat -- SMT
    (ifSat := do
      let model ← Vars.getModel varTerms -- SMT
      ifSat varTerms model)
    (ifUnsat := return none)

/-- Same as `findModelAnd?` but simply returns the model. -/
def findModel? [Monad m] [Vars V] [MonadLiftT IO m]
  (vars : V String) (constraints : Array (Pred V))
: SmtT m (Option (V Int)) :=
  findModelAnd? vars constraints fun _ model => return model



namespace User
/-- User's point of view. -/
def findModel?Demo : IO Unit := do
  let vars : MyVars String := ⟨"n1", "n2", "n3"⟩

  let constraints : Array (Pred MyVars) := #[
    smtFun! terms => 0 < terms.n1,
    smtFun! terms => terms.n2 < 0,
    smtFun! terms => 0 < terms.n3,
    smtFun! terms => 2 * terms.n1 + 3 * terms.n2 = 7 * terms.n3
  ]

  let model? ← findModel? vars constraints |>.run!

  if let some model := model? then
    println! "got a model:"
    println! "- n1 = {model.n1}"
    println! "- n2 = {model.n2}"
    println! "- n3 = {model.n3}"
  else
    println! "no model found"

/-- info:
got a model:
- n1 = 5
- n2 = -1
- n3 = 1
-/
#guard_msgs in
#eval findModel?Demo

end User



/-! ## Minimization

Look for the minimum value of an integer-valued function over some integer variables in some domain
specified by constraints.

The result of this process is a minimal value for the function, and a model for the user's variable
that yields this value. The process might fail, for instance if the domain is empty, in which case
it produces `none`.
-/

/-- Minimization result: smallest value found and its corresponding model. -/
abbrev Minimized? (V : Type → Type) := Option (Int × V Int)

/-- Finds a minimum for `f(vars)` in the space delimited by `constraints`.

Returns the minimum (if any) as a `Minimized? V` along with the number of values of `f` enumerated
to find it.

**NB**: without proper `constraints`, this function may not terminate.
-/
partial def minimize?
  [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [Vars V]
  (vars : V String)
  (f : Fun V Int)
  (constraints : Array (Pred V))
: m (Minimized? V × Nat) :=
  aux constraints none 0
where
  aux constraints (res : Minimized? V) (count : Nat) := do
    -- find a model for the current `constraints`
    let better? ←
      -- find model
      findModelAnd? (m := m) vars constraints
        (fun terms model => do
          -- model found, evaluate `f`
          let f ← f terms
          let val ← Smt.getValue f
          -- return value and model
          return (val, model))
      |>.run

    match better? with
    | .ok (some (val, model)) =>
      -- got a better model add a constraint that the next model should make `f` smaller than `val`
      let constraints := constraints.push
        fun terms => do
          let f ← f terms
          let val ← Term.mkInt val
          smt! f < val
      -- recurse with the new constraint and minimum
      aux constraints (val, model) count.succ
    -- there's no better model, done
    | .ok none => return (res, count)
    | .error e => IO.throwServerError s!"{e}"



namespace User
/-- User's point of view. -/
def minimize?Demo : IO Unit := do
  let vars : MyVars String := ⟨"n1", "n2", "n3"⟩
  let constraints : Array (Pred MyVars) := #[
    smtFun! terms => (-10) ≤ terms.n1 ∧ terms.n1 ≤ 10,
    smtFun! terms => (-10) ≤ terms.n2 ∧ terms.n2 ≤ 10,
    smtFun! terms => (-5) ≤ terms.n3 ∧ terms.n3 ≤ 5
  ]
  let f : Fun MyVars Int :=
    smtFun! terms => -- n1 - 2*n2 + 3* (n3 - n1)
      terms.n1 - 2 * terms.n2 + 3 * (terms.n3 - terms.n1)
  let minimized? ← minimize? vars f constraints
  if let (some (val, model), count) := minimized? then
    println! "done in {count} iteration{if count > 1 then "s" else ""}"
    println! "minimum value is `{val}` on"
    println! "- n1 = {model.n1}"
    println! "- n2 = {model.n2}"
    println! "- n3 = {model.n3}"
  else
    println! "minimization produced no result"

/-- info:
done in 42 iterations
minimum value is `-55` on
- n1 = 10
- n2 = 10
- n3 = -5
-/
#guard_msgs in
#eval minimize?Demo

end User
