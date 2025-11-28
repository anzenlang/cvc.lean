/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc



namespace Cvc.Induction variable [Cvc.Scope]



inductive Typ
| bool
| int
| real
| string

namespace Typ

protected def toString : Typ → String
| bool => "bool"
| int => "int"
| real => "real"
| string => "string"

instance : ToString Typ := ⟨Typ.toString⟩

def toSort : Typ → Env Srt
| bool => Srt.bool
| int => Srt.int
| real => Srt.real
| string => Srt.string

end Typ



class State (S : Type → Type) where
  mapM {m : Type → Type} {α β : Type} : [Monad m] → S α → (α → Typ → m β) → m (S β)
  foldM {m : Type → Type} {α σ : Type} : [Monad m] → S α → (σ → α → Typ → m σ) → σ → m σ

namespace State variable [σ : State S]

def iterM {m : Type → Type} [Monad m] (state : S α) (f : α → Typ → m Unit) : m Unit :=
  σ.foldM state (fun _ => f) ()

protected abbrev Idents [State S] : Type := S String

protected abbrev At [State S] (k : Nat) : Type := S (Symbol.TermAt k)

protected abbrev ValAt [State S] (k : Nat) : Type := S (Symbol.ValAt k)

abbrev Pred : Type := {k : Nat} → (state : σ.At k) → Env Term

abbrev Rel : Type := {k k' : Nat} → (prev : σ.At k) → (curr : σ.At k') → Env Term

abbrev Candidates : Type := Array (σ.Pred × String)

def declareAt (k : Nat) (idents : σ.Idents) : Env (σ.At k) :=
  σ.mapM idents fun ident type => type.toSort >>= Symbol.TermAt.mk ident k

def declareAbstract (idents : σ.Idents) : Env (S Term) :=
  σ.mapM idents fun ident type => type.toSort >>= Term.symbol ident

def getValues (state : σ.At k) (solver : Solver) : Env.Sat (σ.ValAt k) :=
  σ.mapM state fun term _ => term.getValue solver

abbrev ValsAt (k : Nat) : Type := S (Symbol.ValAt k)

inductive Trace? (F : Nat → Type) : Nat → Type
| zero : F 0 → Trace? F 0
| succ : F k.succ → Trace? F k → Trace? F k.succ

abbrev Trace k := Trace? σ.At k

abbrev Cex k := Trace? σ.ValAt k

namespace Trace?

def len (_ : Trace? F k) := k

def highest : Trace? F k → F k
| zero f => f
| succ f _ => f

def atZero : Trace? F k → F 0
| zero f => f
| succ _ tail => tail.atZero

def getCex (solver : Solver) : σ.Trace k → Env.Sat (σ.Cex k)
| zero f0 => zero <$> σ.getValues f0 solver
| succ fk tail => do
  let fk ← σ.getValues fk solver
  succ fk <$> tail.getCex solver

end Trace?

structure Sys [σ : State S] where
  state : σ.Idents
  base : σ.Pred
  step : σ.Rel
  candidates : σ.Candidates

namespace Sys

/-- A candidate index. -/
abbrev Idx (spec : σ.Sys) := Fin spec.candidates.size

end Sys

end State



namespace Sys

section variable [σ : State S] (spec : σ.Sys)

inductive Status
| valid (k : Nat) (strength : RBSet spec.Idx)
| invalid (cex : σ.Cex k) (also : RBSet spec.Idx)
| unknown

namespace Status

def isUnknown : Status spec → Bool
| unknown => true
| valid _ _ | invalid  _ _ => false

def isValid : Status spec → Bool
| valid _ _ => true
| unknown | invalid  _ _ => false

def isInvalid : Status spec → Bool
| invalid _ _ => true
| unknown | valid  _ _ => false

end Status

structure Candidate where
private mk' ::
  idx : spec.Idx
  stepPos : Term
  stepNeg : Term
  status : Status spec

abbrev Candidates := Array (Candidate spec)

namespace Candidates variable {spec} variable (cs : Candidates spec)

def mapUnknownM [Monad m] (f : Candidate spec → m (Candidate spec)) : m (Candidates spec) :=
  cs.mapM fun c => if c.status.isUnknown then f c else return c

def filterMapUnknown (f : Candidate spec → α) : Array α :=
  cs.filterMap fun c => if c.status.isUnknown then f c else none

def filterUnknown : Array (Candidate spec) := cs.filterMapUnknown id

def filterMapValid (f : Candidate spec → α) : Array α :=
  cs.filterMap fun c => if c.status.isValid then f c else none

def filterValid : Array (Candidate spec) := cs.filterMapValid id

def filterMapInvalid (f : Candidate spec → α) : Array α :=
  cs.filterMap fun c => if c.status.isInvalid then f c else none

def filterInvalid : Array (Candidate spec) := cs.filterMapInvalid id

end Candidates

end

end Sys



structure Sys (S : Type → Type) [σ : State S]
extends toSpec : σ.Sys where private mk' ::
  abstractState : S Term
  baseSolver : Solver
  stepSolver : Solver
  candidates' : Sys.Candidates toSpec
  k : Nat
  trace : σ.Trace k

namespace Sys variable [σ : State S]

def mkActlit (desc : String) : Env Term :=
  Term.boolSymbol s!"_actlit_candidate_{desc}_"

def mkActlitFor {spec : σ.Sys} (candidateIdx : spec.Idx) (desc : String) : Env Term :=
  mkActlit s!"{candidateIdx}_{desc}"

namespace Candidate

def mk {spec : σ.Sys} (idx : spec.Idx) : Env (Candidate spec) := do
  let stepPos ← mkActlitFor idx "step_positive"
  let stepNeg ← mkActlitFor idx "step_negative"
  return ⟨idx, stepPos, stepNeg, .unknown⟩

end Candidate

namespace Candidates

def mk (spec : σ.Sys) : Env (Candidates spec) := do
  spec.candidates.mapFinIdxM fun idx _ h => Candidate.mk ⟨idx, h⟩

end Candidates

def mk (spec : σ.Sys) : Env (Sys S) := do
  let candidates ← Candidates.mk spec
  let abstractState ← σ.declareAbstract spec.state
  let at0 ← σ.declareAt 0 spec.state
  let baseSolver ← Solver.mk "induction base solver" true
  baseSolver.setOption "produce-models" "true"
  baseSolver.setOption "produce-unsat-cores" "true"
  spec.base at0 >>= baseSolver.assert
  let stepSolver ← Solver.mk "induction reverse-step solver" true
  stepSolver.setOption "produce-models" "true"
  stepSolver.setOption "produce-unsat-cores" "true"
  for candidate in candidates do
    spec.candidates[candidate.idx].fst at0
    >>= Term.not
    >>= stepSolver.activeAssert (act := candidate.stepNeg)
  return ⟨spec, abstractState, baseSolver, stepSolver, candidates, 0, .zero at0⟩

section variable (sys : Sys S)

def isDone : Bool :=
  ¬ sys.candidates'.any fun c => c.status.isUnknown

abbrev Idx := sys.toSpec.Idx

def candidatePred (idx : sys.Idx) : σ.Pred := sys.candidates[idx].fst
def candidateDesc (idx : sys.Idx) : String := sys.candidates[idx].snd

def print (sys : Sys S) (pref : String := "") (withState : Bool := false) : Env Unit := do
  if withState then
    println! "{pref}state"
    σ.iterM sys.abstractState fun (symbol : Term) typ => do
      println! "{pref}- {← symbol.toSmtString} | {typ}"
  println! "{pref}candidates"
  for c in sys.candidates' do
    match c.status with
    | .unknown => println! "{pref}-[{c.idx}]-[unknown] \"{sys.candidateDesc c.idx}\""
    | .valid k set => do
      println! "{pref}-[{c.idx}]-[valid@{k}] \"{sys.candidateDesc c.idx}\""
      if 1 < set.size then println! "{pref}    proved in cluster {set.toList}"
    | .invalid trace set => do
      println! "{pref}-[{c.idx}]-[invalid@{trace.len}] \"{sys.candidateDesc c.idx}\""
      if 1 < set.size then println! "{pref}    falsified in cluster {set.toList}"

def unroll : Env ((sys' : Sys S) ×' sys'.k = sys.k + 1) := do
  let atK := sys.trace.highest
  let atNextK ← σ.declareAt sys.k.succ sys.toSpec.state
  let trace : σ.Trace sys.k.succ := sys.trace.succ atNextK
  -- base: unroll forward
  let step ← sys.step atK atNextK
  sys.baseSolver.assert step
  -- step: unroll backward
  let step ← sys.step atNextK atK
  sys.stepSolver.assert step
  -- step actlits
  for c in sys.candidates'.filterUnknown do
    let pred ← sys.candidatePred c.idx atNextK
    sys.stepSolver.activeAssert c.stepPos pred
  return ⟨{sys with k := sys.k.succ, trace}, rfl⟩

def checkBase' : Env ((sys' : Sys S) ×' sys'.k = sys.k + 1) := do
  let ⟨sys', h_sys'⟩ ← loop sys sys.candidates'.size.succ
  h_sys' ▸ sys'.unroll
where
  loop (sys : Sys S) : Nat → Env ((sys' : Sys S) ×' sys'.k = sys.k)
  | 0 => throwInternal s!"[checkBase] maximal number of iterations reached"
  | n + 1 => do
    let solver := sys.baseSolver
    -- sanity, make sure base solver is sat
    let res ← solver.checkSat?
    if res.isSat? ≠ some true then
      throwInternal s!"illegal base solver state, expected `sat` but got `{res}`"
    let unknown := sys.candidates'.filterUnknown
    let state := sys.trace.highest
    let mut anyBadCandidate ← Term.bool false
    for candidate in unknown do
      let pred ← sys.candidatePred candidate.idx state
      anyBadCandidate ← pred.not >>= anyBadCandidate.or
    solver.checkSat #[anyBadCandidate]
      (ifUnsat := return ⟨sys, rfl⟩)
      (ifSat := do
        let cex ← sys.trace.getCex solver
        let falsified : RBSet sys.Idx ←
          unknown.foldlM (init := RBSet.empty) fun set candidate => do
            let pred ← sys.candidatePred candidate.idx state
            let isValid ← solver.getValue pred >>= Term.boolVal
            return if isValid then set else set.insert candidate.idx
        let candidates' := sys.candidates'.mapUnknownM (m := Id)
          fun candidate =>
            if candidate.idx ∈ falsified
            then {candidate with status := .invalid cex falsified}
            else candidate
        let sys := {sys with candidates'}
        if sys.isDone then return ⟨sys, rfl⟩ else loop sys n)

def checkBase : Env (Sys S) := PSigma.fst <$> sys.checkBase'

def checkStep'
: (valid : 0 < sys.k := by (try simp) <;> grind)
→ Env ((sys' : Sys S) ×' sys'.k = sys.k) :=
  fun _ => loop sys sys.candidates'.filterUnknown sys.candidates'.size.succ
where
  checkIsSat (solver : Solver) (desc : String) : Env Unit := do
    solver.logComment fun () => s!"sanity, make sure step solver is sat - {desc}"
    if let some core ← solver.checkUnsatCore? then
      let msg ←
        s!"illegal step solver state ({desc}), expected `sat` but got `unsat`\nunsat core:"
        |> core.foldlM (return s!"{·}\n- {← Term.toSmtString ·}")
      throwInternal msg
  loop (sys : Sys S) (unknown : Candidates sys.toSpec)
  : Nat → Env ((sys' : Sys S) ×' sys'.k = sys.k)
  | 0 => throwInternal s!"[checkStep] maximal number of iterations reached"
  | n + 1 => do
    let solver := sys.stepSolver
    checkIsSat solver "unrolling only"
    let mut actlits := #[]
    let mut anyBadCandidate ← Term.bool false
    for candidate in unknown do
      anyBadCandidate ← anyBadCandidate.or candidate.stepNeg
      actlits := actlits ++ #[candidate.stepPos]
    checkIsSat solver "unrolling and positive actlits"
    solver.checkSat (actlits.push anyBadCandidate)
      (ifSat := do
        let state := sys.trace.atZero
        let unknown ← unknown.filterM
          fun c => do
            let pred ← sys.candidatePred c.idx state
            solver.getValue pred >>= Term.boolVal
        if unknown.isEmpty then return ⟨sys, rfl⟩ else loop sys unknown n)
      (ifUnsat := do
        let validSet := RBSet.empty |> unknown.foldl fun set c => set.insert c.idx
        let candidates' ← sys.candidates'.mapUnknownM fun candidate =>
          if candidate.idx ∈ validSet
          then return {candidate with status := .valid sys.k validSet}
          else return candidate
        return ⟨{sys with candidates'}, rfl⟩)

def checkStep (valid : 0 < sys.k := by (try simp) <;> grind) : Env (Sys S) :=
  PSigma.fst <$> sys.checkStep' valid

def checkBaseAndStep : Env (Sys S) := do
  if sys.isDone then return sys
  let ⟨sys, _⟩ ← sys.checkBase'
  if sys.isDone then return sys
  let ⟨sys, _⟩ ← sys.checkStep'
  return sys

end

def run (sys : Sys S)
: (n : Nat)
→ (beforeLoopingDo : Sys S → Env Unit := fun _ => return ())
→ Env (Sys S)
| 0, _ => return sys
| n + 1, beforeLoopingDo => do
  let sys ← sys.checkBaseAndStep
  if sys.isDone then return sys
  beforeLoopingDo sys
  sys.run n beforeLoopingDo

end Sys
