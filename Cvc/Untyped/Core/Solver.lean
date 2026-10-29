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
import all Cvc.Untyped.Core.BVar

public import Cvc.Basic
public import Cvc.Basic.Env
public import Cvc.Srt
public import Cvc.Logic
public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.Core.BVar
public import Cvc.Untyped.Core.Bool
public import Cvc.Gen.SolverMode
public import Cvc.SolverOptions



/-! # The solver, sort-erased

Three things live here:

- `Solver` itself, and the `Result` a check-sat produces;
- the three monadic environments that record *which answer the solver just gave, and which solver
  gave it*, so that a query only valid after one answer cannot be written after another, nor
  addressed to a different solver;
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

/-- A SyGuS grammar.

A grammar belongs to the scope, as a term does: cvc5 builds one through a solver
(`Solver.mkGrammar`), but any solver of the same term manager accepts it. The rule builders live in
`Cvc.Untyped.Grammar`; the type is declared here because the interpolant and abduct queries
below take one.
-/
structure Grammar [Ω] where private mk' ::
  private raw : cvc5.Grammar
  /-- The parameters the grammar was built over.

  A `synth-fun` restricted by the grammar must be declared over these very variables, which is
  what lets a grammar whose parameters were made out of sight, by `smt.grammar!`, be used for one.
  -/
  boundVars : BVars
  /-- The sort of the grammar's start symbol.

  cvc5 offers no way to read a grammar's non-terminals back, so the sort is recorded when the
  grammar is built; it is what lets the grammar be typed after the fact.
  -/
  startSrt : Srt

/-- String representation, as the SyGuS pre-declaration and rule set. -/
protected def Grammar.toString [Ω] (g : Grammar) : String := toString g.raw

instance [Ω] : ToString Grammar := ⟨Grammar.toString⟩



/-! ## Solver-mode monadic environments

A check-sat splits the world into three, and the queries that make sense differ in each: a model
exists only when the answer was sat, an unsat core only when it was unsat, a timeout core only
when it was unknown.

Each answer therefore gets its own monad, wrapping `EnvT` privately. Since the wrapper is private,
user code cannot lift arbitrary `EnvT` code — a check-sat in particular — into one of them, so a
sat-only block cannot smuggle in a query that would invalidate the very answer it stands on.

**Each is also indexed by the solver that answered**, `s.EnvSatT m α` rather than `EnvSatT m α`,
and that catches the other mistake two solvers in one scope invite: a block standing on one
solver's answer querying another solver. Every modal query carries the index —
`getValue : s.EnvSat Term` — and `checkSat`'s branches are typed at the solver it was called on, so
asking `s₂` for a value inside `s₁`'s sat branch does not typecheck rather than answering about the
wrong model.

The two mechanisms are separate and both are needed: the private lift is about *when* a query may
be written, the index about *what* it may be written against.

`env_gen%` comes from `Cvc.Gen.SolverMode`; the private lift it generates is private to *this*
module, which is what lets `checkSat` below enter these monads and nothing else.

**Every modal query also has an unchecked twin in `Env`**, named with a trailing `!` —
`getValue!`, `getUnsatCore!` — for code that knows the answer by other means. It gives up both
guarantees: nothing checks that the solver last answered as the query needs, or that it is the
solver which answered. cvc5 still refuses some queries made in the wrong state, at run time.
-/
namespace Solver variable [Ω] [Monad m]


/-- Sat-specific modal environment. -/
structure EnvSatT (solver : Solver) (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvSatT / EnvSat

/-- Unsat-specific modal environment. -/
structure EnvUnsatT (solver : Solver) (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnsatT / EnvUnsat

/-- Unknown-specific modal environment. -/
structure EnvUnknownT (solver : Solver) (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnknownT / EnvUnknown

end Solver



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

/-- Sets an option in a solver. -/
def setOpt (opt : Solver.Option) (val : opt.argType) : Env Unit :=
  let (opt, val) := opt.toStrings val
  s.setOption opt val

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

variable {s : Solver} (e : Unknown.Explanation) (dumpAssertions : Bool := false)

/-- Fails because sat was unexpected, showing the assertions if `dumpAssertions`. -/
def unexpectedSat : s.EnvSat α := s.unexpectedResult "sat" dumpAssertions
/-- Fails because unsat was unexpected, showing the assertions if `dumpAssertions`. -/
def unexpectedUnsat : s.EnvUnsat α := s.unexpectedResult "unsat" dumpAssertions
/-- Fails because unknown was unexpected, showing the assertions if `dumpAssertions`. -/
def unexpectedUnknown : s.EnvUnknown α :=
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

/-- Declares a function symbol of the sort `α` denotes. -/
def declareFunAs (α : Type) [ToTyp α] (symbol : String) (fresh : Bool := true) : Env Term := do
  let srt ← Srt.of α
  if let (some dom, some cod) := (srt.getFunctionDomainSorts?, srt.getFunctionCodomainSort?) then
    s.declareFun symbol dom cod fresh
  else
    s.declareConst symbol srt fresh

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



/-! ### Quantifier elimination, interpolants and abducts

cvc5 answers the null term when there is no interpolant or abduct to give, and when an enumeration
is exhausted. The functions that can be answered that way return an `Option`, `none` standing for
the null term, so that no null term ever reaches a caller.
-/

/-- `none` for the null term, the term itself otherwise. -/
private def nonNull? (t : cvc5.Term) : Option Term := if t.isNull then none else some t

@[inherit_doc S.getQuantifierElimination]
def qe (q : Term) : Env Term := runUnsafe' do s.toUnsafe.getQuantifierElimination q

/-- Partial quantifier elimination, `none` if cvc5 answers the null term.

See `cvc5.Solver.getQuantifierEliminationDisjunct` for what the disjuncts are, and how repeated
calls compute the full elimination incrementally.
-/
def qeDisjunct (q : Term) : Env (Option Term) :=
  runUnsafe' do return nonNull? (← s.toUnsafe.getQuantifierEliminationDisjunct q)

/-- An interpolant of the assertions and `conj`, `none` if cvc5 finds none.

An interpolant is a formula `I` over the symbols the assertions `A` and `conj` share, such that
`A → I` and `I → conj`. A `grammar` restricts the shape of `I`. Needs `produce-interpolants`.
-/
def getInterpolant (conj : Term) (grammar : Option Grammar := none) : Env (Option Term) :=
  runUnsafe' do
    let t ← match grammar with
      | none => s.toUnsafe.getInterpolant conj
      | some g => s.toUnsafe.getInterpolantOfGrammar conj g.raw
    return nonNull? t

/-- The next interpolant, `none` when there is no other.

Only legal right after a successful `getInterpolant` or `getNextInterpolant`. Needs
`incremental`, which is on by default.
-/
def getNextInterpolant : Env (Option Term) :=
  runUnsafe' do return nonNull? (← s.toUnsafe.getInterpolantNext)

/-- An abduct of the assertions and `conj`, `none` if cvc5 finds none.

An abduct is a formula `B` such that the assertions `A` and `B` are consistent and `A ∧ B → conj`.
A `grammar` restricts the shape of `B`. Needs `produce-abducts`.

When no abduct exists, cvc5 may search for one indefinitely rather than answer: asking for an
abduct of `false` does not return.
-/
def getAbduct (conj : Term) (grammar : Option Grammar := none) : Env (Option Term) :=
  runUnsafe' do
    let t ← match grammar with
      | none => s.toUnsafe.getAbduct conj
      | some g => s.toUnsafe.getAbductOfGrammar conj g.raw
    return nonNull? t

/-- The next abduct, `none` when there is no other.

Only legal right after a successful `getAbduct` or `getNextAbduct`. Needs `incremental`, which
is on by default.
-/
def getNextAbduct : Env (Option Term) :=
  runUnsafe' do return nonNull? (← s.toUnsafe.getAbductNext)



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
  (ifSat : s.EnvSatT m α := s.unexpectedSat)
  (ifUnsat : s.EnvUnsatT m α := s.unexpectedUnsat)
  (ifUnknown : Unknown.Explanation → s.EnvUnknownT m α := liftM ∘ s.unexpectedUnknown)
: EnvT m α := do
  match ← s.checkIsSat? (assuming := assuming) with
  | .inl true => ifSat.toEnv
  | .inl false => ifUnsat.toEnv
  | .inr unkExpl => ifUnknown unkExpl |>.toEnv

@[inherit_doc checkSatResult]
def checkSat? {α : Type} (s : Solver) (assuming : Option Terms := none)
  (ifSat : s.EnvSatT m (Option α) := return none)
  (ifUnsat : s.EnvUnsatT m (Option α) := return none)
  (ifUnknown : Unknown.Explanation → s.EnvUnknownT m (Option α) := liftM ∘ s.unexpectedUnknown)
: EnvT m (Option α) :=
  s.checkSat assuming ifSat ifUnsat ifUnknown

end check_sat



/-! ### Where the answer was sat -/

@[inherit_doc S.getValue]
def getValue (term : Term) : s.EnvSat Term := runUnsafe' do s.toUnsafe.getValue term

@[inherit_doc S.getValue]
abbrev _root_.Cvc.Untyped.Term.getValue {s: Solver} (term : Term) : s.EnvSat Term := s.getValue term

@[inherit_doc S.getValues]
def getValues (terms : Terms) : s.EnvSat Terms := runUnsafe' do s.toUnsafe.getValues terms

/-- The value the model gives a term, as the Lean value `α` denotes. -/
def getValueAs (α : Type) [TermToValue α] (term : Term) : s.EnvSat α := do
  Term.extractValue (α := α) (← s.getValue term)

/-- The values the model gives some terms, as the Lean values `α` denotes. -/
def getValuesAs (α : Type) [TermToValue α] (terms : Terms) : s.EnvSat (Array α) := do
  (← s.getValues terms).mapM fun value => (Term.extractValue value : s.EnvSat α)

@[inherit_doc S.getModelDomainElements]
def getModelDomainElements (sort : Srt) : s.EnvSat Terms :=
  runUnsafe' do s.toUnsafe.getModelDomainElements sort

@[inherit_doc S.isModelCoreSymbol]
def isModelCoreSymbol (term : Term) : s.EnvSat Bool :=
  runUnsafe' do s.toUnsafe.isModelCoreSymbol term

@[inherit_doc S.getModel]
def getModelAsString (sorts : Srts) (consts : Terms) : s.EnvSat String :=
  runUnsafe' do s.toUnsafe.getModel sorts consts

@[inherit_doc S.blockModel]
def blockModel (mode : Model.BlockMode) : s.EnvSat Unit :=
  runUnsafe' do s.toUnsafe.blockModel mode.toUnsafe

@[inherit_doc S.blockModelValues]
def blockModelValues (terms : Terms) : s.EnvSat Unit :=
  runUnsafe' do s.toUnsafe.blockModelValues terms

/-- `getValue` in `Env`, not checked to follow a sat answer. -/
def getValue! (term : Term) : Env Term := (s.getValue term).toEnv

/-- `getValue` in `Env`, not checked to follow a sat answer.

The solver is explicit, there being no expected mode monad to infer it from.
-/
abbrev _root_.Cvc.Untyped.Term.getValueIn! (term : Term) (s : Solver) : Env Term := s.getValue! term

/-- `getValues` in `Env`, not checked to follow a sat answer. -/
def getValues! (terms : Terms) : Env Terms := (s.getValues terms).toEnv

/-- `getValueAs` in `Env`, not checked to follow a sat answer. -/
def getValueAs! (α : Type) [TermToValue α] (term : Term) : Env α := (s.getValueAs α term).toEnv

/-- `getValuesAs` in `Env`, not checked to follow a sat answer. -/
def getValuesAs! (α : Type) [TermToValue α] (terms : Terms) : Env (Array α) :=
  (s.getValuesAs α terms).toEnv

/-- `getModelDomainElements` in `Env`, not checked to follow a sat answer. -/
def getModelDomainElements! (sort : Srt) : Env Terms := (s.getModelDomainElements sort).toEnv

/-- `isModelCoreSymbol` in `Env`, not checked to follow a sat answer. -/
def isModelCoreSymbol! (term : Term) : Env Bool := (s.isModelCoreSymbol term).toEnv

/-- `getModelAsString` in `Env`, not checked to follow a sat answer. -/
def getModelAsString! (sorts : Srts) (consts : Terms) : Env String :=
  (s.getModelAsString sorts consts).toEnv

/-- `blockModel` in `Env`, not checked to follow a sat answer. -/
def blockModel! (mode : Model.BlockMode) : Env Unit := (s.blockModel mode).toEnv

/-- `blockModelValues` in `Env`, not checked to follow a sat answer. -/
def blockModelValues! (terms : Terms) : Env Unit := (s.blockModelValues terms).toEnv



/-! ### Where the answer was unsat -/

@[inherit_doc S.getUnsatAssumptions]
def getUnsatAssumptions : s.EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatAssumptions

@[inherit_doc S.getUnsatCore]
def getUnsatCore : s.EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCore

@[inherit_doc S.getUnsatCoreLemmas]
def getUnsatCoreLemmas : s.EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCoreLemmas

@[inherit_doc S.getProof]
def getUnsatProof (pc : Proof.Component := .full) : s.EnvUnsat (s.Proofs pc) :=
  runUnsafe' do s.toUnsafe.getProof pc.toUnsafe

/-- `getUnsatAssumptions` in `Env`, not checked to follow an unsat answer. -/
def getUnsatAssumptions! : Env Terms := s.getUnsatAssumptions.toEnv

/-- `getUnsatCore` in `Env`, not checked to follow an unsat answer. -/
def getUnsatCore! : Env Terms := s.getUnsatCore.toEnv

/-- `getUnsatCoreLemmas` in `Env`, not checked to follow an unsat answer. -/
def getUnsatCoreLemmas! : Env Terms := s.getUnsatCoreLemmas.toEnv

/-- `getUnsatProof` in `Env`, not checked to follow an unsat answer. -/
def getUnsatProof! (pc : Proof.Component := .full) : Env (s.Proofs pc) :=
  (s.getUnsatProof pc).toEnv



/-! ### Where the answer was unknown -/

@[inherit_doc S.getTimeoutCore]
def getTimeoutCore : s.EnvUnknown (Result × Terms) := runUnsafe' do
  let (res, terms) ← s.toUnsafe.getTimeoutCore
  return (Result.ofUnsafe res, terms)

@[inherit_doc S.getTimeoutCoreAssuming]
def getTimeoutCoreAssuming (assumptions : Terms) : s.EnvUnknown (Result × Terms) := runUnsafe' do
  let (res, terms) ← s.toUnsafe.getTimeoutCoreAssuming assumptions
  return (Result.ofUnsafe res, terms)

/-- `getTimeoutCore` in `Env`, not checked to follow an unknown answer. -/
def getTimeoutCore! : Env (Result × Terms) := s.getTimeoutCore.toEnv

/-- `getTimeoutCoreAssuming` in `Env`, not checked to follow an unknown answer. -/
def getTimeoutCoreAssuming! (assumptions : Terms) : Env (Result × Terms) :=
  (s.getTimeoutCoreAssuming assumptions).toEnv

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
