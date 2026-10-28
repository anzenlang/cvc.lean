/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Core.Symbols



namespace Cvc.Typed public section variable [Ω]

namespace Symbols.Sig

/-- An array of named predicates over `SVars`. -/
abbrev Candidates [Symbols SVars] := Array (String × SVars.PredAt')

end Symbols.Sig

namespace Sys

/-- A trace of types at decreasing depth. -/
inductive Trace (α : Nat → Type) : (k : Nat) → Type
| zero : α 0 → Trace α 0
| cons : α (k + 1) → Trace α k → Trace α (k + 1)

namespace Trace

def iterM [Monad m] (f : {k : Nat} → α k → m Unit) : Trace α k → m Unit
| zero val => f val
| cons val tl => do tl.iterM f ; f val

def getCurrent : Trace α k → α k
| zero val => val
| cons val _ => val

def getZero : Trace α k → α 0
| zero val => val
| cons _ tl => tl.getZero

end Trace

end Sys

namespace Symbols variable [Symbols SVars]

namespace Sig

/-- A trace of unrolled `Term`-symbols. -/
abbrev TermTrace := Sys.Trace (SVars.TermsAt)
/-- A trace of Lean-values for some unrolled symbols. -/
abbrev ValueTrace := Sys.Trace (SVars.ValuesAt)
/-- A trace of `Term`-values for some unrolled symbols. -/
abbrev TermValueTrace := Sys.Trace (SVars.TermValuesAt)

/-- Extracts the Lean-values of a `TermTrace`. -/
def ValueTrace.extract {s : Solver} : SVars.TermTrace k → s.EnvSat (SVars.ValueTrace k)
| .zero terms => .zero <$> terms.getValues s
| .cons terms tl => do
  let values ← terms.getValues s
  .cons values <$> extract tl

@[inherit_doc ValueTrace.extract]
def TermTrace.getValues := @ValueTrace.extract
@[inherit_doc TermTrace.getValues]
def TermTrace.getCex := @TermTrace.getValues

/-- Extracts the `Term`-values of a `TermTrace` -/
def TermValueTrace.extract {s : Solver} : SVars.TermTrace k → s.EnvSat (SVars.TermValueTrace k)
| .zero terms => .zero <$> terms.getTermValues s
| .cons terms tl => do
  let values ← terms.getTermValues s
  .cons values <$> extract tl

@[inherit_doc TermValueTrace.extract]
def TermTrace.getTermValues := @TermValueTrace.extract
@[inherit_doc TermTrace.getTermValues]
def TermTrace.getTermCex := @TermTrace.getTermValues

end Sig

export Sig (TermTrace ValueTrace TermValueTrace)

end Symbols



structure Sys (SVars : Symbols.Sig) [Symbols SVars] where
  /-- State variable identifiers. -/
  idents : SVars.Idents
  /-- Initial predicate over `SVars`. -/
  init : SVars.PredAt'
  /-- Transition relation over `SVars`. -/
  next : SVars.RelAt'
  /-- Candidate properties over the system. -/
  candidates : SVars.Candidates

abbrev Symbols.Sig.Sys := @Typed.Sys

namespace Sys variable [Symbols SVars] (sys : SVars.Sys) (solver : Solver)

def initAt (solver : Solver) (k : Nat) : Env (Term Bool) := do
  let svs_k ← solver.declareSymbolsAt k sys.idents
  sys.init svs_k

def nextAt (curr : SVars.TermsAt k) (next : SVars.TermsAt k') : Env (Term Bool) := do
  sys.next curr next



/-- Bounded model checking of a system, unrolled `k` steps.

Holds what unrolling needs from the system — its identifiers, its transition relation and the
candidates not falsified yet — beside the solver, the trace of the steps declared so far and the
counterexamples found, each with the candidates it falsified.
-/
structure Bmc (SVars : Symbols.Sig) [Symbols SVars] (k : Nat) where
private mk' ::
  /-- The system's state variables. -/
  idents : SVars.Idents
  /-- The transition relation, at this scope. -/
  next : {k k' : Nat} → SVars.TermsAt k → SVars.TermsAt k' → Env (Term Bool)
  /-- The candidate invariants not falsified yet, at this scope. -/
  candidates : Array (String × ({k : Nat} → SVars.TermsAt k → Env (Term Bool)))
  solver : Solver
  sVars : SVars.TermTrace k
  falsified : List ((k : Nat) × SVars.ValueTrace k × Array String)
  actlitCounter : Nat

abbrev _root_.Cvc.Typed.Symbols.Sig.Bmc := @Cvc.Typed.Sys.Bmc

namespace Bmc variable [Symbols SVars] {k : Nat}

def mk (sys : SVars.Sys) : Env (SVars.Bmc 0) := do
  let sVars0 ← sys.idents.declareAt 0
  let init0 ← sys.init sVars0
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  solver.assert init0
  return {
    idents := sys.idents
    next := fun curr next => sys.next curr next
    candidates := sys.candidates.map fun (name, pred) => (name, fun state => pred state)
    solver, falsified := [], sVars := Trace.zero sVars0, actlitCounter := 0
  }

def isDone (bmc : SVars.Bmc k) : Bool := bmc.candidates.isEmpty

def check (bmc : SVars.Bmc k) : Env (Option <| Array String × SVars.Bmc k) := do
  if bmc.isDone then return none
  let state := bmc.sVars.getCurrent
  let candidates ← bmc.candidates.mapM fun (name, pred) => return (name, ← pred state)
  let orArgs ← bmc.candidates.mapM (fun (_, pred) => pred state >>= Term.not)
  let assuming ← Term.orN' orArgs
  let satRes? ← bmc.solver.checkSat? #[assuming]
    (ifSat := do
      let falsified ← candidates.filterMapM fun (name, pred) => do
        let isTrue ← bmc.solver.getValue pred
        if isTrue then return none else return some name
      let cex ← bmc.sVars.getCex
      return some (falsified, cex))
  if let some (falsifiedCandidates, cex) := satRes? then
    let candidates := bmc.candidates.filter fun (name, _) => name ∉ falsifiedCandidates
    let falsified := ⟨k, cex, falsifiedCandidates⟩ :: bmc.falsified
    return some (falsifiedCandidates, {bmc with candidates, falsified})
  else return none

def unroll (bmc : SVars.Bmc k) : Env (SVars.Bmc k.succ) := do
  let nextState ← bmc.idents.declareAt k.succ
  let next ← bmc.next bmc.sVars.getCurrent nextState
  -- println! "asserting {next}"
  bmc.solver.assert next
  return { bmc with sVars := .cons nextState bmc.sVars }

end Bmc


end Sys
