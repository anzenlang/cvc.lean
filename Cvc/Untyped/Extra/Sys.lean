/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core.Symbols



namespace Cvc.Untyped public section variable [Ω]

namespace Symbols.Sig

/-- An array of named predicates over `SVars`. -/
abbrev Candidates [Symbols SVars] := Array (String × SVars.FunAt')

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
/-- A trace of Lean-values for unrolled symbols. -/
abbrev ValueTrace := Sys.Trace (SVars.ValuesAt)
/-- A trace of `Term`-values for unrolled symbols. -/
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

/-- Extracts the `Term`-values of a `TermTrace` -/
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



/-- A transition system over symbols `SV`. -/
structure Sys (SVars : Symbols.Sig) [Symbols SVars] where
  idents : SVars.Idents
  init : SVars.FunAt'
  next : SVars.Fun2At'
  candidates : SVars.Candidates

@[inherit_doc Untyped.Sys]
abbrev Symbols.Sys := @Untyped.Sys
@[inherit_doc Untyped.Sys]
abbrev Symbols.Sig.Sys := @Untyped.Sys

namespace Sys variable [Symbols SVars] (sys : SVars.Sys) (solver : Solver)

/-- Declares symbols and builds the term for the initial predicate at `k`. -/
def initAt (solver : Solver) (k : Nat) : Env Term := do
  solver.declareSymbolsAt k sys.idents >>= sys.init

/-- Builds the term for the transition predicate between `k` and `k'`, **no symbol declaration**. -/
def nextAt (curr : SVars.TermsAt k) (next : SVars.TermsAt k') : Env Term :=
  sys.next curr next



/-- Bounded model checking of a system, unrolled `k` steps.

Holds what unrolling needs from the system — its identifiers, its transition relation and the
candidates not falsified yet — beside the solver, the trace of the steps declared so far and the
counterexamples found, each with the candidates it falsified.
-/
structure Bmc (SV : Symbols.Sig) [Symbols SV] (k : Nat) where
private mk' ::
  /-- The system's state variables. -/
  idents : SV.Idents
  /-- The transition relation, at this scope. -/
  next : {k k' : Nat} → SV.TermsAt k → SV.TermsAt k' → Env Term
  /-- The candidate invariants not falsified yet, at this scope. -/
  candidates : Array (String × ({k : Nat} → SV.TermsAt k → Env Term))
  solver : Solver
  sVars : SV.TermTrace k
  falsified : List ((k : Nat) × SV.ValueTrace k × Array String)
  actlitCounter : Nat

@[inherit_doc Cvc.Untyped.Sys.Bmc]
abbrev _root_.Cvc.Untyped.Symbols.Bmc := @Cvc.Untyped.Sys.Bmc
@[inherit_doc Cvc.Untyped.Sys.Bmc]
abbrev _root_.Cvc.Untyped.Symbols.Sig.Bmc := @Cvc.Untyped.Sys.Bmc

namespace Bmc variable [Symbols S] {k : Nat}

/-- Constructor. -/
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
        let isTrue ← bmc.solver.getValueAs Bool pred
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
