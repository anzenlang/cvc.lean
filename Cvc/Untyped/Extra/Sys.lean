/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core.Symbols



/-! # Transition systems and bounded model checking, sort-erased

A `Sys` is a transition system over a symbol structure: an initial predicate, a transition relation
and named candidate invariants, each a function of the symbols at one step or two.

`Sys.Bmc` checks the candidates by bounded model checking. `Bmc.mk` starts at step `0`; `check`
answers the candidates some run reaching the current step falsifies, and is called again until it
answers `none`; `unroll` then moves to the next step. `isDone` holds once no candidate is left.
-/

namespace Cvc.Untyped public section variable [Ω]

namespace Symbols.Sig

/-- An array of named predicates over `SVars`. -/
abbrev Candidates [Symbols SVars] := Array (String × SVars.FunAt')

end Symbols.Sig

namespace Sys

/-- One value per step from `0` to `k`, the latest first. -/
inductive Trace (α : Nat → Type) : (k : Nat) → Type
| zero : α 0 → Trace α 0
| cons : α (k + 1) → Trace α k → Trace α (k + 1)

namespace Trace

/-- Runs `f` on each step's value, from step `0` up. -/
def iterM [Monad m] (f : {k : Nat} → α k → m Unit) : Trace α k → m Unit
| zero val => f val
| cons val tl => do tl.iterM f ; f val

/-- The value at the latest step, `k`. -/
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

/-- The symbols of each step, as terms. -/
abbrev TermTrace := Sys.Trace (SVars.TermsAt)
/-- The values of each step's symbols, as Lean values. -/
abbrev ValueTrace := Sys.Trace (SVars.ValuesAt)
/-- The values of each step's symbols, as terms. -/
abbrev ValueTermTrace := Sys.Trace (SVars.ValueTermsAt)

/-- The values the model gives a `TermTrace`, as Lean values. -/
def ValueTrace.extract {s : Solver} : SVars.TermTrace k → s.EnvSat (SVars.ValueTrace k)
| .zero terms => .zero <$> terms.getValues s
| .cons terms tl => do
  let values ← terms.getValues s
  .cons values <$> extract tl

@[inherit_doc ValueTrace.extract]
def TermTrace.getValues := @ValueTrace.extract
@[inherit_doc TermTrace.getValues]
def TermTrace.getCex := @TermTrace.getValues

/-- The values the model gives a `TermTrace`, as terms. -/
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



/-- A transition system over the symbol structure `SVars`. -/
structure Sys (SVars : Symbols.Sig) [Symbols SVars] where
  /-- The state variables' identifiers. -/
  idents : SVars.Idents
  /-- The initial predicate. -/
  init : SVars.FunAt'
  /-- The transition relation, from one step to the next. -/
  next : SVars.Fun2At'
  /-- The candidate invariants, by name. -/
  candidates : SVars.Candidates

@[inherit_doc Untyped.Sys]
abbrev Symbols.Sys := @Untyped.Sys
@[inherit_doc Untyped.Sys]
abbrev Symbols.Sig.Sys := @Untyped.Sys

namespace Sys variable [Symbols SVars] (sys : SVars.Sys) (solver : Solver)

/-- Declares the symbols of step `k` in `solver`, and builds the initial predicate over them. -/
def initAt (solver : Solver) (k : Nat) : Env Term := do
  solver.declareSymbolsAt k sys.idents >>= sys.init

/-- The transition predicate from step `k` to step `k'`, over symbols already declared. -/
def nextAt (curr : SVars.TermsAt k) (next : SVars.TermsAt k') : Env Term :=
  sys.next curr next



/-- Bounded model checking of a system, unrolled to step `k`. -/
structure Bmc (SV : Symbols.Sig) [Symbols SV] (k : Nat) where
private mk' ::
  /-- The system's state variables. -/
  idents : SV.Idents
  /-- The transition relation. -/
  next : {k k' : Nat} → SV.TermsAt k → SV.TermsAt k' → Env Term
  /-- The candidate invariants not falsified yet. -/
  candidates : Array (String × ({k : Nat} → SV.TermsAt k → Env Term))
  /-- The solver the unrolling is asserted in. -/
  solver : Solver
  /-- The state variables of every step so far. -/
  sVars : SV.TermTrace k
  /-- The counterexamples found, the latest first.

  Each holds its step, its trace, and the candidates it falsified.
  -/
  falsified : List ((k : Nat) × SV.ValueTrace k × Array String)

@[inherit_doc Cvc.Untyped.Sys.Bmc]
abbrev _root_.Cvc.Untyped.Symbols.Bmc := @Cvc.Untyped.Sys.Bmc
@[inherit_doc Cvc.Untyped.Sys.Bmc]
abbrev _root_.Cvc.Untyped.Symbols.Sig.Bmc := @Cvc.Untyped.Sys.Bmc

namespace Bmc variable [Symbols S] {k : Nat}

/-- Starts checking `sys` at step `0`, in a solver of its own. -/
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

/-- The candidates some run reaching step `k` falsifies, and the checker without them.

The counterexample is recorded in `falsified`. Answers `none` when no candidate left is falsified at
this step, and fails if the solver gives up.
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
        let isTrue ← bmc.solver.getValueAs Bool pred
        if isTrue then return none else return some name
      let cex ← bmc.sVars.getCex
      return some (falsified, cex))
  if let some (falsifiedCandidates, cex) := satRes? then
    let candidates := bmc.candidates.filter fun (name, _) => name ∉ falsifiedCandidates
    let falsified := ⟨k, cex, falsifiedCandidates⟩ :: bmc.falsified
    return some (falsifiedCandidates, {bmc with candidates, falsified})
  else return none

/-- Moves to step `k + 1`, asserting the transition to it. -/
def unroll (bmc : SVars.Bmc k) : Env (SVars.Bmc k.succ) := do
  let nextState ← bmc.idents.declareAt k.succ
  let next ← bmc.next bmc.sVars.getCurrent nextState
  -- println! "asserting {next}"
  bmc.solver.assert next
  return { bmc with sVars := .cons nextState bmc.sVars }

end Bmc


end Sys
