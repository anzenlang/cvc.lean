/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Theory.Arith
public import Cvc.Untyped.Core.Symbols
public import Cvc.Untyped.Core.Solver



/-! # A linear-arithmetic solver over a symbols structure

`LinSolve.run` takes the symbols to declare and named constraints over them, and answers either a
model, as Lean values, or the names of the constraints an unsat core holds. The symbols are a
`structure.symbols`, so a model's values are read off by field name.
-/
namespace Cvc.Untyped.Examples public section



namespace LinSolve open Cvc Untyped variable {Syms : Symbols.Sig}

/-- What `run` answers. -/
inductive Result (S : Symbols Syms)
| sat (values : Syms.Values)
| unsat (core : Array String)
| unknown
| error (e : Error)

/-- A solver holding the symbols and the named constraints asserted over them. -/
structure State [Ω] (S : Symbols Syms) where
  solver : Solver
  terms : Syms.Terms
  constraints : Array (String × Term)

namespace State variable [Ω] [S : Symbols Syms]

/-- Declares the symbols on a fresh solver and asserts the constraints. -/
def init (vars : Syms.Idents) (constraints : Array (String × Syms.Fun)) : Env (State S) := do
  let terms ← vars.declare
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  solver.setOption "produce-unsat-cores" "true"
  let constraints ← constraints.mapM fun (name, pred) => do
    let c ← pred terms
    solver.assert c
    return (name, c)
  return {solver, terms, constraints}

section variable (state : State S)

/-- The symbols' values in the model. -/
def getValues : state.solver.EnvSat Syms.Values :=
  state.solver.getSymbolValues state.terms

/-- The names of the constraints in the unsat core. -/
def getUnsatCore : state.solver.EnvUnsat (Array String) := do
  let core ← state.solver.getUnsatCore
  let mut core' := Array.mkEmpty core.size
  for term in core do
    let some (name, _) := state.constraints.find? (fun (_, term') => term == term')
      | throwInternal s!"unknown constraint {term}"
    core' := core'.push name
  return core'

/-- Checks the constraints, answering a model, an unsat core or `unknown`. -/
def check : Env (Result S) := do
  state.solver.checkSat
    (ifSat := Result.sat <$> state.getValues)
    (ifUnsat := Result.unsat <$> state.getUnsatCore)
    (ifUnknown := fun _ => return .unknown)

end

end State



/-- Solves `constraints` over `symbols`, in a scope of its own. -/
def run [S : Symbols Syms]
  (symbols : Syms.Idents) (constraints : [Ω] → Array (String × Syms.Fun))
: BaseIO (Result S) := do
  let res ← Env.run do
    let state ← State.init symbols constraints
    state.check
  match res with
  | .ok res => return res
  | .error e => return .error e

end LinSolve




namespace LinSolve

namespace Test1 open scoped Cvc.Untyped

/-- Three rational unknowns. -/
structure.symbols Syms where
  x : Rat
  y : Rat
  z : Rat

namespace Constraints variable [Ω]

def c1 : String × Syms.Fun := ("c1", fun terms =>
  smt! 2. * terms.x + terms.y + (- 1.) * terms.z ≤ 0.)

def c2 : String × Syms.Fun := ("c2", fun terms =>
  smt! terms.x + terms.y + terms.z ≥ 5.)

def c3 : String × Syms.Fun := ("c3", fun terms =>
  smt! 3. * terms.x + (- 5.) * terms.y + terms.z ≥ 5.)

def sat := #[c1, c2, c3]

def c4 : String × Syms.Fun := ("c4", fun terms =>
  smt! 2. * terms.x + terms.y + (- 1.) * terms.z > 0.)

def unsat := sat.push c4

end Constraints

/-- Solves `constraints` and prints the answer. -/
def test (constraints : [Ω] → Array (String × Syms.Fun)) : IO Unit := do
  match ← LinSolve.run Syms.idents constraints with
  | .sat values =>
    println! "sat:\n- x := {values.x}\n- y := {values.y}\n- z := {values.z}"
  | .unsat core =>
    println! "unsat by{core.foldl (init := "") (s!"{·}\n- {·}")}"
  | .unknown => println! "failed to reach a conclusion"
  | .error e => println! "an error occurred\n{e}"

/--
info: sat:
- x := 15/11
- y := 5/11
- z := 35/11
-/
#guard_msgs in #eval test Constraints.sat

/--
info: unsat by
- c1
- c4
-/
#guard_msgs in #eval test Constraints.unsat

end Test1
