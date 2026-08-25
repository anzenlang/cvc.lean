/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Theory.Arith
public import Cvc.Typed.Symbols
public import Cvc.Typed.Solver



namespace LinSolve open Cvc Typed variable {Syms : Symbols.Sig}

inductive Result (S : Symbols Syms)
| sat (values : S.Values)
| unsat (core : Array String)
| unknown
| error (e : Error)

structure State [Ω] (S : Symbols Syms) where
  solver : Solver
  terms : S.Terms
  constraints : Array (String × Term Bool)

namespace State variable [Ω] [S : Symbols Syms]

def init (vars : S.Idents) (constraints : Array (String × S.Pred)) : Env (State S) := do
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

def getValues : state.solver.EnvSat Syms.Values :=
  state.solver.getSymbolValues state.terms

def getUnsatCore : state.solver.EnvUnsat (Array String) := do
  let core ← state.solver.getUnsatCore
  let mut core' := Array.mkEmpty core.size
  for term in core do
    let some (name, _) := state.constraints.find? (fun (_, term') => term == term')
      | throwInternal s!"unknown constraint {term}"
    core' := core'.push name
  return core'

def check : Env (Result S) := do
  state.solver.checkSat
    (ifSat := Result.sat <$> state.getValues)
    (ifUnsat := Result.unsat <$> state.getUnsatCore)

end

end State



def run [S : Symbols Syms]
  (symbols : S.Idents) (constraints : Array (String × S.Pred))
: BaseIO (Result S) := do
  let res ← Env.run do
    let state ← State.init symbols constraints
    state.check
  match res with
  | .ok res => return res
  | .error e => return .error e

end LinSolve




namespace LinSolve

namespace Test1 open scoped Cvc.Typed

/-- Symbol structure with all necessary helpers. -/
structure.symbols Syms where
  x : Rat
  y : Rat
  z : Rat

namespace Constraints

def c1 : String × Syms.Pred := ("c1", fun terms =>
  smt! 2. * terms.x + terms.y + (- 1.) * terms.z ≤ 0.)

def c2 : String × Syms.Pred := ("c2", fun terms =>
  smt! terms.x + terms.y + terms.z ≥ 5.)

def c3 : String × Syms.Pred := ("c3", fun terms =>
  smt! 3. * terms.x + (- 5.) * terms.y + terms.z ≥ 5.)

def sat := #[c1, c2, c3]

def c4 : String × Syms.Pred := ("c4", fun terms =>
  smt! 2. * terms.x + terms.y + (- 1.) * terms.z > 0.)

def unsat := sat.push c4

end Constraints

def testSat : IO Unit := do
  let idents := Syms.idents
  match ← LinSolve.run idents Constraints.sat with
  | .sat values =>
    println! "sat:\n- x := {values.x}\n- y := {values.y}\n- z := {values.z}"
  | .unsat core =>
    println! "unsat by{core.foldl (init := "") (s!"{·}\n{·}")}"
  | .unknown => println! "failed to reach a conclusion"
  | .error e => println! "an error occurred\n{e}"

/--
info: sat:
- x := 15/11
- y := 5/11
- z := 35/11
-/
#guard_msgs in #eval testSat

def testUnsat : IO Unit := do
  let idents := Syms.idents
  match ← LinSolve.run idents Constraints.unsat with
  | .sat values =>
    println! "sat:\n- x := {values.x}\n- y := {values.y}\n- z := {values.z}"
  | .unsat core =>
    println! "unsat by{core.foldl (init := "") (s!"{·}\n- {·}")}"
  | .unknown => println! "failed to reach a conclusion"
  | .error e => println! "an error occurred\n{e}"

/--
info: unsat by
- c1
- c4
-/
#guard_msgs in #eval testUnsat

end Test1
