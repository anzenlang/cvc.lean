/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Core.Symbols



/-! # Transition systems and bounded model checking, typed

A `Sys` is a transition system over a symbol structure of state variables (see `structure.symbols`):
an initial predicate, a transition relation between a state and the next, and named candidate
invariants. `Sys.Bmc` checks the candidates on runs of increasing length.

`Sys.Bmc.mk sys` starts at step `0`. `check` looks for a run whose state at the current step
falsifies some remaining candidates: it answers their names and the checker without them, the
counterexample recorded in `falsified`, or `none` once no remaining candidate can be falsified at
this step. `unroll` then moves to the next step.
-/

namespace Cvc.Typed public section variable [Ω]

namespace Symbols.Sig

/-- Named candidate invariants: predicates over the state variables, at any step. -/
abbrev Candidates [Symbols SVars] := Array (String × SVars.PredAt')

end Symbols.Sig

namespace Sys

/-- One value per step, from step `k` down to step `0`: an `α i` at step `i`. -/
inductive Trace (α : Nat → Type) : (k : Nat) → Type
| zero : α 0 → Trace α 0
| cons : α (k + 1) → Trace α k → Trace α (k + 1)

namespace Trace

/-- Runs `f` on each step's value, from step `0` up to step `k`. -/
def iterM [Monad m] (f : {k : Nat} → α k → m Unit) : Trace α k → m Unit
| zero val => f val
| cons val tl => do tl.iterM f ; f val

/-- The value at step `k`, the last one. -/
def getCurrent : Trace α k → α k
| zero val => val
| cons val _ => val

/-- The value at step `0`. -/
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
abbrev ValueTermTrace := Sys.Trace (SVars.ValueTermsAt)

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

/-- Extracts the `Term`-values of a `TermTrace`. -/
def ValueTermTrace.extract {s : Solver} : SVars.TermTrace k → s.EnvSat (SVars.ValueTermTrace k)
| .zero terms => .zero <$> terms.getValueTerms s
| .cons terms tl => do
  let values ← terms.getValueTerms s
  .cons values <$> extract tl

@[inherit_doc ValueTermTrace.extract]
def TermTrace.getValueTerms := @ValueTermTrace.extract
@[inherit_doc TermTrace.getValueTerms]
def TermTrace.getTermCex := @TermTrace.getValueTerms

end Sig

export Sig (TermTrace ValueTrace ValueTermTrace)

end Symbols



/-- A transition system over the state variables `SVars`, with candidate invariants to check. -/
structure Sys (SVars : Symbols.Sig) [Symbols SVars] where
  /-- State variable identifiers. -/
  idents : SVars.Idents
  /-- Initial predicate over `SVars`. -/
  init : SVars.PredAt'
  /-- Transition relation over `SVars`. -/
  next : SVars.RelAt'
  /-- Candidate properties over the system. -/
  candidates : SVars.Candidates

/-- `Sys SVars`, written `SVars.Sys`. -/
abbrev Symbols.Sig.Sys := @Typed.Sys

namespace Sys variable [Symbols SVars] (sys : SVars.Sys) (solver : Solver)

/-- Declares step `k`'s state variables in `solver`, and answers the initial predicate on them. -/
def initAt (solver : Solver) (k : Nat) : Env (Term Bool) := do
  let svs_k ← solver.declareSymbolsAt k sys.idents
  sys.init svs_k

/-- The transition relation from the state `curr` to the state `next`. -/
def nextAt (curr : SVars.TermsAt k) (next : SVars.TermsAt k') : Env (Term Bool) := do
  sys.next curr next



/-- Bounded model checking of a system, unrolled to step `k`. -/
structure Bmc (SVars : Symbols.Sig) [Symbols SVars] (k : Nat) where
private mk' ::
  /-- The system's state variables. -/
  idents : SVars.Idents
  /-- The transition relation, at this scope. -/
  next : {k k' : Nat} → SVars.TermsAt k → SVars.TermsAt k' → Env (Term Bool)
  /-- The candidate invariants not falsified yet, at this scope. -/
  candidates : Array (String × ({k : Nat} → SVars.TermsAt k → Env (Term Bool)))
  /-- The solver the steps are asserted in. -/
  solver : Solver
  /-- The state variables of every step so far. -/
  sVars : SVars.TermTrace k
  /-- The counterexamples found, latest first: each one's step, trace and falsified candidates. -/
  falsified : List ((k : Nat) × SVars.ValueTrace k × Array String)

/-- `Sys.Bmc SVars k`, written `SVars.Bmc k`. -/
abbrev _root_.Cvc.Typed.Symbols.Sig.Bmc := @Cvc.Typed.Sys.Bmc

namespace Bmc variable [Symbols SVars] {k : Nat}

/-- A checker for `sys` at step `0`, on a new solver asserting the initial predicate. -/
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
    solver, falsified := [], sVars := Trace.zero sVars0
  }

/-- Whether every candidate has been falsified. -/
def isDone (bmc : SVars.Bmc k) : Bool := bmc.candidates.isEmpty

/-- Looks for a run whose state at the current step falsifies some remaining candidates.

Answers their names and the checker without them, the counterexample added to `falsified`, or
`none` if no remaining candidate can be falsified at this step. Call it until it answers `none`.
-/
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

/-- Moves to the next step: declares its state variables and asserts the transition into it. -/
def unroll (bmc : SVars.Bmc k) : Env (SVars.Bmc k.succ) := do
  let nextState ← bmc.idents.declareAt k.succ
  let next ← bmc.next bmc.sVars.getCurrent nextState
  bmc.solver.assert next
  return { bmc with sVars := .cons nextState bmc.sVars }

end Bmc


end Sys
