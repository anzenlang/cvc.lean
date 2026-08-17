/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.BVar

public import Cvc.Basic
public import Cvc.Basic.Env
public import Cvc.Srt
public import Cvc.Logic
public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.BVar
public import Cvc.Untyped.Mode



/-! # The solver, sort-erased

Three things live here:

- `Solver` itself, and the `Result` a check-sat produces;
- the three monadic environments that record *which answer the solver just gave*, so that a query
  only valid after one answer cannot be written after another;
- every solver function whose signature mentions no term, and which is therefore shared verbatim
  by both layers rather than re-typed.

A function whose signature does mention a term — asserting a formula, reading a value, an unsat
core — is not here: those are the ones the typed layer states more precisely.
-/
namespace Cvc.Untyped public section

/-- A solver instance. -/
def Solver [Ω] := cvc5.Solver

/-- A proof produced by some solver. -/
def Solver.Proof [Ω] : (solver : Solver) → (pc : Proof.Component) → Type := 𝕂² cvc5.Proof

/-- An array of `Solver.Proof`. -/
abbrev Solver.Proofs [Ω] (solver : Solver) (pc : Proof.Component) : Type :=
  Array (solver.Proof pc)



/-! ## Solver-mode monadic environments

A check-sat splits the world into three, and the queries that make sense differ in each: a model
exists only when the answer was sat, an unsat core only when it was unsat, a timeout core only
when it was unknown.

Each answer therefore gets its own monad, wrapping `EnvT` privately. Since the wrapper is private,
user code cannot lift arbitrary `EnvT` code — a check-sat in particular — into one of them, so a
sat-only block cannot smuggle in a query that would invalidate the very answer it stands on.

`env_gen%` comes from `Cvc/Untyped/Mode.lean`; the private lift it generates is private to
*this* module, which is what lets `checkSat` below enter these monads and nothing else.
-/
section variable [Ω] [Monad m]


/-- Code running where the solver last answered sat. -/
structure EnvSatT [Ω] (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvSatT / EnvSat

/-- Code running where the solver last answered unsat. -/
structure EnvUnsatT (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnsatT / EnvUnsat

/-- Code running where the solver last answered unknown. -/
structure EnvUnknownT (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnknownT / EnvUnknown

end



namespace Solver variable [Ω] open cvc5 renaming Solver → S

/-- Creates a new solver. -/
def new : Env Solver := runUnsafe (S.new ·)

section variable [Monad m] [MonadLiftT BaseIO m] (s : Solver)

/-- Conversion to cvc5. -/
private def toUnsafe : S := s
/-- Constructor from cvc5. -/
private def ofUnsafe : S → Solver := id



/-! ### The result of a check-sat -/

/-- What a check-sat answered. -/
def Result := cvc5.Result

namespace Result

private def toUnsafe : Result → cvc5.Result := id
private def ofUnsafe : cvc5.Result → Result := id

section variable (r : Result)

protected def toString : String := r.toUnsafe.toString
instance : ToString Result := ⟨Result.toString⟩

private def isSat! : Bool := r.toUnsafe.isSat
private def isUnsat! : Bool := r.toUnsafe.isUnsat
private def getUnknownExplanation? : Option Unknown.Explanation :=
  r.toUnsafe.getUnknownExplanation? |>.map Unknown.Explanation.ofUnsafe

/-- Sat as a boolean, or why the solver gave up. -/
abbrev Sat? := Bool ⊕ Unknown.Explanation

/-- The answer, or why the solver gave up. -/
def isSat? : Res Sat? :=
  if r.isSat! then return .inl true
  else if r.isUnsat! then return .inl false
  else if let some unkExpl := r.getUnknownExplanation? then return .inr unkExpl
  else throwInternal s!"check result is neither sat, unsat, or unknown\n{r}"

/-- The answer, failing if the solver gave up. -/
def isSat : Res Bool := r.isSat? >>= fun
  | .inl res => return res
  | .inr unkExpl => throwUser s!"unexpected unknown result: {unkExpl}"

end

end Result



/-! ### Options and information -/

@[inherit_doc S.getVersion]
def getVersion : Env String := runUnsafe' do s.toUnsafe.getVersion

@[inherit_doc S.setOption]
def setOption (option value : String) : Env Unit := runUnsafe' do
  s.toUnsafe.setOption option value

@[inherit_doc S.getOption]
def getOption (flag : String) : Env String := runUnsafe' do s.toUnsafe.getOption flag

@[inherit_doc S.getOptionNames]
def getOptionNames : Env (Array String) := runUnsafe' do s.toUnsafe.getOptionNames

@[inherit_doc S.setInfo]
def setInfo (option value : String) : Env Unit := runUnsafe' do
  s.toUnsafe.setInfo option value

@[inherit_doc S.getInfo]
def getInfo (flag : String) : Env String := runUnsafe' do s.toUnsafe.getInfo flag

@[inherit_doc S.getInstantiations]
def getInstantiations : Env String := runUnsafe' do s.toUnsafe.getInstantiations



/-! ### The logic -/

@[inherit_doc S.setLogic]
def setLogic (logic : Logic) : Env Unit := runUnsafe' do s.toUnsafe.setLogic logic.toSmtLib

@[inherit_doc S.isLogicSet]
def isLogicSet : Env Bool := runUnsafe' do s.toUnsafe.isLogicSet

/-- The logic as its SMT-LIB name. -/
def getLogicString : Env String := runUnsafe' do s.toUnsafe.getLogic

@[inherit_doc getLogicString]
def getLogic : Env Logic := s.getLogicString >>= liftM ∘ Logic.ofSmtLib



/-! ### Assertion scopes -/

@[inherit_doc S.resetAssertions]
def reset : Env Unit := runUnsafe' do s.toUnsafe.resetAssertions

@[inherit_doc S.push]
def push (nscopes : UInt32 := 1) : Env Unit := runUnsafe' do s.toUnsafe.push nscopes

@[inherit_doc S.pop]
def pop (nscopes : UInt32 := 1) : Env Unit := runUnsafe' do s.toUnsafe.pop nscopes



/-! ### Declaring sorts -/

@[inherit_doc S.declareSort]
def declareSrt (symbol : String) (arity : UInt32) (fresh : Bool := false) : Env Srt := do
  Srt.checkFreshSortSymbol symbol
  let srt ← runUnsafe' do s.toUnsafe.declareSort symbol arity fresh
  registerSort symbol srt
  return srt



/-! ### Rejecting an unexpected answer

These are what a check-sat branch falls back on when the caller did not expect that answer. They
mention no term, so both layers share them.
-/

section unexpected

/-- The assertions, as SMT-LIB, for an error message. -/
private def assertionsForError : Env (Array String) := do
  let assertions ← runUnsafe' do s.toUnsafe.getAssertions
  return assertions.map toString

private def unexpectedResult (badResDesc : String) (dumpAssertions : Bool)
  (explanation : Option String := none)
: Env α := do
  let mut msg := s!"unexpected `{badResDesc}` result"
  if let some e := explanation then msg := s!"{msg}\n- {e}"
  if dumpAssertions then
    let assertions ← s.assertionsForError
    if assertions.isEmpty then
      msg := s!"{msg}, solver does not have any assertions"
    else
      msg := msg ++ " for the following assertions\n```smtlib"
        |> assertions.foldl (s!"{·}\n(assert {·})")
      msg := msg ++ "\n```"
  throwUser msg

variable (e : Unknown.Explanation) (dumpAssertions : Bool := false)

/-- Fails because sat was unexpected, showing the assertions if `dumpAssertions`. -/
def unexpectedSat : EnvSat α := s.unexpectedResult "sat" dumpAssertions
/-- Fails because unsat was unexpected, showing the assertions if `dumpAssertions`. -/
def unexpectedUnsat : EnvUnsat α := s.unexpectedResult "unsat" dumpAssertions
/-- Fails because unknown was unexpected, showing the assertions if `dumpAssertions`. -/
def unexpectedUnknown : EnvUnknown α :=
  s.unexpectedResult "unknown" dumpAssertions (explanation := toString e)

end unexpected



/-! ### Assertions

From here on every signature mentions a term, so the typed layer states these more precisely.
-/

@[inherit_doc S.getAssertions]
def getAssertions : Env Terms := runUnsafe' do s.toUnsafe.getAssertions

@[inherit_doc S.assertFormula]
def assert (t : Term) : Env Unit := runUnsafe' do s.toUnsafe.assertFormula t

@[inherit_doc S.getLearnedLiterals]
def getLearnedLiterals (t : LearnedLitType := LearnedLitType.input) : Env Terms :=
  runUnsafe' do s.toUnsafe.getLearnedLiterals t.toUnsafe



/-! ### Declarations and definitions -/

@[inherit_doc S.declareFun]
def declareFun (symbol : String) (sorts : Srts) (sort : Srt) (fresh : Bool := true) : Env Term :=
  runUnsafe' do s.toUnsafe.declareFun symbol sorts sort fresh

/-- Declares a constant symbol of the given sort. -/
def declareConst (symbol : String) (sort : Srt) (fresh : Bool := true) : Env Term :=
  s.declareFun symbol #[] sort fresh

@[inherit_doc S.defineFun]
def defineFun (symbol : String) (bvs : BVars) (sort : Srt) (body : Term)
  (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFun symbol bvs sort body global

/-- Defines a constant symbol as the given body. -/
def defineConst (symbol : String) (sort : Srt) (body : Term) (global : Bool := false) : Env Term :=
  s.defineFun symbol #[] sort body global

@[inherit_doc S.defineFunRec]
def defineFunRec (symbol : String) (bvs : BVars) (sort : Srt) (body : Term)
  (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFunRec symbol bvs sort body global

@[inherit_doc S.defineFunRecTerm]
def defineFunRecTerm (fn : Term) (bvs : BVars) (body : Term) (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFunRecTerm fn bvs body global

@[inherit_doc S.defineFunsRec]
def defineFunsRec (funs : Terms) (bvs : Array BVars) (bodies : Terms)
  (global : Bool := false)
: (valid : bvs.size = bodies.size := by grind) → Env Unit := fun _ =>
  runUnsafe' do s.toUnsafe.defineFunsRec funs bvs bodies global



/-! ### Quantifier elimination, interpolants and abducts -/

@[inherit_doc S.getQuantifierElimination]
def qe (q : Term) : Env Term := runUnsafe' do s.toUnsafe.getQuantifierElimination q

@[inherit_doc S.getQuantifierEliminationDisjunct]
def qeDisjunct (q : Term) : Env Term :=
  runUnsafe' do s.toUnsafe.getQuantifierEliminationDisjunct q

@[inherit_doc S.getInterpolant]
def getInterpolant (conj : Term) (grammar : Option Grammar := none) : Env Term :=
  runUnsafe' do
    match grammar with
    | none => s.toUnsafe.getInterpolant conj
    | some g => s.toUnsafe.getInterpolantOfGrammar conj g

@[inherit_doc S.getInterpolantNext]
def getNextInterpolant : Env Term := runUnsafe' do s.toUnsafe.getInterpolantNext

@[inherit_doc S.getAbduct]
def getAbduct (conj : Term) (grammar : Option Grammar := none) : Env Term :=
  runUnsafe' do
    match grammar with
    | none => s.toUnsafe.getAbduct conj
    | some g => s.toUnsafe.getAbductOfGrammar conj g

@[inherit_doc S.getAbductNext]
def getNextAbduct : Env Term := runUnsafe' do s.toUnsafe.getAbductNext



/-! ### Checking satisfiability

`checkSat` is the only way into the mode monads: it runs the branch matching the answer the solver
actually gave. A branch the caller did not supply rejects that answer.
-/

section check_sat variable (assuming : Option Terms := none)

/-- Checks the satisfiability of the constraints asserted so far. -/
def checkSatResult : Env Result := do
  let code := if let some terms := assuming then S.checkSatAssuming s terms else S.checkSat s
  Result.ofUnsafe <$> runUnsafe' code

@[inherit_doc checkSatResult]
def checkIsSat? : Env Result.Sat? := do (← s.checkSatResult assuming).isSat?

@[inherit_doc checkSatResult]
def checkIsSat : Env Bool := do (← s.checkSatResult assuming).isSat

@[inherit_doc checkSatResult]
def checkSat
  (ifSat : EnvSatT m α := s.unexpectedSat)
  (ifUnsat : EnvUnsatT m α := s.unexpectedUnsat)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m α := liftM ∘ s.unexpectedUnknown)
: EnvT m α := do
  match ← s.checkIsSat? (assuming := assuming) with
  | .inl true => ifSat.toEnv
  | .inl false => ifUnsat.toEnv
  | .inr unkExpl => ifUnknown unkExpl |>.toEnv

@[inherit_doc checkSatResult]
def checkSat? {α : Type} (s : Solver) (assuming : Option Terms := none)
  (ifSat : EnvSatT m (Option α) := return none)
  (ifUnsat : EnvUnsatT m (Option α) := return none)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m (Option α) := liftM ∘ s.unexpectedUnknown)
: EnvT m (Option α) :=
  s.checkSat assuming ifSat ifUnsat ifUnknown

end check_sat



/-! ### Where the answer was sat -/

@[inherit_doc S.getValue]
def getValue (term : Term) : EnvSat Term := runUnsafe' do s.toUnsafe.getValue term

@[inherit_doc S.getValues]
def getValues (terms : Terms) : EnvSat Terms := runUnsafe' do s.toUnsafe.getValues terms

/-- The value the model gives a term, as the Lean value `α` denotes. -/
def getValueAs (α : Type) [TermToValue α] (term : Term) : EnvSat α := do
  Term.getValue (α := α) (← s.getValue term)

/-- The values the model gives some terms, as the Lean values `α` denotes. -/
def getValuesAs (α : Type) [TermToValue α] (terms : Terms) : EnvSat (Array α) := do
  (← s.getValues terms).mapM fun value => (Term.getValue value : EnvSat α)

@[inherit_doc S.getModelDomainElements]
def getModelDomainElements (sort : Srt) : EnvSat Terms :=
  runUnsafe' do s.toUnsafe.getModelDomainElements sort

@[inherit_doc S.isModelCoreSymbol]
def isModelCoreSymbol (term : Term) : EnvSat Bool :=
  runUnsafe' do s.toUnsafe.isModelCoreSymbol term

@[inherit_doc S.getModel]
def getModelAsString (sorts : Srts) (consts : Terms) : EnvSat String :=
  runUnsafe' do s.toUnsafe.getModel sorts consts

@[inherit_doc S.blockModel]
def blockModel (mode : Model.BlockMode) : EnvSat Unit :=
  runUnsafe' do s.toUnsafe.blockModel mode.toUnsafe

@[inherit_doc S.blockModelValues]
def blockModelValues (terms : Terms) : EnvSat Unit :=
  runUnsafe' do s.toUnsafe.blockModelValues terms



/-! ### Where the answer was unsat -/

@[inherit_doc S.getUnsatAssumptions]
def getUnsatAssumptions : EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatAssumptions

@[inherit_doc S.getUnsatCore]
def getUnsatCore : EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCore

@[inherit_doc S.getUnsatCoreLemmas]
def getUnsatCoreLemmas : EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCoreLemmas

@[inherit_doc S.getProof]
def getUnsatProof (pc : Proof.Component := .full) : EnvUnsat (s.Proofs pc) :=
  runUnsafe' do s.toUnsafe.getProof pc.toUnsafe



/-! ### Where the answer was unknown -/

@[inherit_doc S.getTimeoutCore]
def getTimeoutCore : EnvUnknown (Result × Terms) := runUnsafe' do
  let (res, terms) ← s.toUnsafe.getTimeoutCore
  return (Result.ofUnsafe res, terms)

@[inherit_doc S.getTimeoutCoreAssuming]
def getTimeoutCoreAssuming (assumptions : Terms) : EnvUnknown (Result × Terms) := runUnsafe' do
  let (res, terms) ← s.toUnsafe.getTimeoutCoreAssuming assumptions
  return (Result.ofUnsafe res, terms)

end

namespace Proof variable {solver : Solver} (p : solver.Proof pc)

@[inherit_doc cvc5.Proof.getRule]
def getRule : ProofRule := cvc5.Proof.getRule p

@[inherit_doc cvc5.Proof.getResult]
def getResult : Term := cvc5.Proof.getResult p

@[inherit_doc cvc5.Proof.getArguments]
def getArguments : Terms := cvc5.Proof.getArguments p

@[inherit_doc cvc5.Proof.getChildren]
def getChildren : solver.Proofs pc := cvc5.Proof.getChildren p

/-- Get the proof rewrite rule used by the root step of the proof, if it has one.

Answers `none` unless `getRule` is `ProofRule.DSL_REWRITE` or `ProofRule.THEORY_REWRITE`: those two
rules are the only ones carrying a rewrite rule.

See also `getRewriteRule`, which takes that condition as a hypothesis instead of answering an
`Option`.
-/
def getRewriteRule? : Option ProofRewriteRule := cvc5.Proof.getRewriteRule? p

/-- Get the proof rewrite rule used by the root step of the proof.

Requires that `getRule` returns `ProofRule.DSL_REWRITE` or `ProofRule.THEORY_REWRITE`; cvc5 fails
otherwise. Matching on `getRule` is where the hypothesis comes from:

```lean
match h : p.getRule with
| .DSL_REWRITE => some (p.getRewriteRule (.inl h))
| .THEORY_REWRITE => some (p.getRewriteRule (.inr h))
| _ => none
```
-/
def getRewriteRule : p.getRule = .DSL_REWRITE ∨ p.getRule = .THEORY_REWRITE → ProofRewriteRule :=
  𝕂 cvc5.Proof.getRewriteRule! p

/-- String representation. -/
def toString : Env String := Env.lift5 <| cvc5.Solver.proofToString solver p .NONE

/-- String representation with formatter. -/
def toStringFmt (fmt : Proof.Format := default)
: (valid : fmt = .no ∨ pc = .full := by grind) → Env String :=
  𝕂 Env.lift5 <| cvc5.Solver.proofToString solver p fmt.toUnsafe

end Proof

end Solver
