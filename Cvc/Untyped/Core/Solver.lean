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

`Solver`, the `Result` a check-sat produces, and the functions driving a solver: options,
assertions, declarations, `checkSat`, and the queries its answer allows.
-/
-- The typed layer's `Solver` is an abbreviation of this one: it inherits every function here that
-- mentions no term, and re-types the others.
namespace Cvc.Untyped public section

/-- A solver instance. -/
def Solver [Ω] := cvc5.Solver

/-- A proof, indexed by the solver that produced it and the `Proof.Component` it was asked for.

Obtained with `getUnsatProof`, where the answer was unsat.
-/
def Solver.Proof [Ω] : (solver : Solver) → (pc : Proof.Component) → Type := 𝕂² cvc5.Proof

/-- An array of `Solver.Proof`. -/
abbrev Solver.Proofs [Ω] (solver : Solver) (pc : Proof.Component) : Type :=
  Array (solver.Proof pc)

/-- Two proofs are equal when they are the same step: cvc5 compares proofs by identity.

cvc5 shares a sub-proof between the steps that use it, so a step reached along two paths is equal
to itself. It also builds the same step twice on occasion, and the two copies are different proofs
that happen to conclude the same thing: identity, not structure.
-/
instance Solver.Proof.instBEq [Ω] {solver : Solver} : BEq (solver.Proof pc) :=
  inferInstanceAs (BEq cvc5.Proof)

/-- A proof's hash, consistent with its identity. -/
instance Solver.Proof.instHashable [Ω] {solver : Solver} : Hashable (solver.Proof pc) :=
  inferInstanceAs (Hashable cvc5.Proof)

/-- A SyGuS grammar, restricting the terms a synthesis, interpolation or abduction may answer.

Built by `Solver.mkGrammar` or `smt.grammar!` (`Cvc.Untyped.Grammar`); any solver of the scope
accepts it, not only the one that built it.
-/
structure Grammar [Ω] where private mk' ::
  private raw : cvc5.Grammar
  /-- The parameters the grammar was built over.

  A `synthFun` restricted by the grammar must be declared over these very variables.
  -/
  boundVars : BVars
  /-- The sort of the grammar's start symbol. -/
  startSrt : Srt
-- `startSrt` is recorded because cvc5 offers no way to read a grammar's non-terminals back; it is
-- what lets the grammar be typed after the fact.
--
-- Declared here rather than beside its builders because the interpolant and abduct queries below
-- take one.

/-- String representation, as the SyGuS pre-declaration and rule set. -/
protected def Grammar.toString [Ω] (g : Grammar) : String := toString g.raw

instance [Ω] : ToString Grammar := ⟨Grammar.toString⟩



/-! ## Solver-mode monadic environments

A check-sat splits the world into three, and the queries that make sense differ in each: a model
exists only when the answer was sat, an unsat core only when it was unsat, a timeout core only when
it was unknown. Each answer therefore gets its own monad — `EnvSat`, `EnvUnsat`, `EnvUnknown` —
that only `checkSat` enters, and into which no `Env` code, a check-sat in particular, can be lifted.

Each is also indexed by the solver that answered, `s.EnvSat`, so asking `s₂` for a value inside
`s₁`'s sat branch does not typecheck.

Every modal query has an unchecked twin in `Env`, named with a trailing `!` (`getValue!`,
`getUnsatCore!`), for code that knows the answer by other means. Nothing checks that the solver last
gave the answer the query needs, nor that it is the solver which gave it; cvc5 still refuses some
queries made in the wrong state.
-/
-- Each monad wraps `EnvT` privately, and `env_gen%` (from `Cvc.Gen.SolverMode`) generates a lift
-- private to *this* module, which is what lets `checkSat` enter these monads and nothing else. The
-- private lift is about *when* a query may be written, the solver index about *what* against.
namespace Solver variable [Ω] [Monad m]


/-- Code running where `solver` last answered sat: the model queries (`getValue`, …) live here.

Entered only through `checkSat`'s `ifSat` branch.
-/
structure EnvSatT (solver : Solver) (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvSatT / EnvSat

/-- Code running where `solver` last answered unsat: unsat cores and proofs live here.

Entered only through `checkSat`'s `ifUnsat` branch.
-/
structure EnvUnsatT (solver : Solver) (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnsatT / EnvUnsat

/-- Code running where `solver` last answered unknown: timeout cores live here.

Entered only through `checkSat`'s `ifUnknown` branch.
-/
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

/-- Sets an option given as data, its value typed: `s.setOpt .smt_produceModels true`. -/
def setOpt (opt : Solver.Option) (val : opt.argType) : Env Unit :=
  let (opt, val) := opt.toStrings val
  s.setOption opt val

/-- The value of the option named `flag`.

```smtlib
(get-option <keyword>)
```
-/
def getOption (flag : String) : Env String := runUnsafe' do s.toUnsafe.getOption flag

/-- The names of all the options `setOption` and `getOption` accept. -/
def getOptionNames : Env (Array String) := runUnsafe' do s.toUnsafe.getOptionNames

/-- Sets the info flag `option` to `value`.

```smtlib
(set-info <attribute>)
```
-/
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

/-- The logic, parsed from its SMT-LIB name. -/
def getLogic : Env Logic := s.getLogicString >>= liftM ∘ Logic.ofSmtLib



/-! ### Assertion scopes -/

@[inherit_doc S.resetAssertions]
def reset : Env Unit := runUnsafe' do s.toUnsafe.resetAssertions

@[inherit_doc S.push]
def push (nscopes : UInt32 := 1) : Env Unit := runUnsafe' do s.toUnsafe.push nscopes

@[inherit_doc S.pop]
def pop (nscopes : UInt32 := 1) : Env Unit := runUnsafe' do s.toUnsafe.pop nscopes



/-! ### Declaring sorts -/

/-- Declares an uninterpreted sort of the given arity, named `symbol`.

Fails if a sort of that name was already declared in the scope.
-/
def declareSrt (symbol : String) (arity : UInt32) : Env Srt := do
  Srt.checkFreshSortSymbol symbol
  let srt ← runUnsafe' do s.toUnsafe.declareSort symbol arity (fresh := true)
  registerSort symbol srt
  return srt
-- cvc5's `fresh := false` would answer the sort already declared under a name, but a name is
-- declared at most once per scope here.



/-! ### Rejecting an unexpected answer

What a check-sat branch falls back on when the caller did not expect that answer.
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



/-! ### Assertions -/

@[inherit_doc S.getAssertions]
def getAssertions : Env Terms := runUnsafe' do s.toUnsafe.getAssertions

/-- Asserts a formula. -/
def assert (t : Term) : Env Unit := runUnsafe' do s.toUnsafe.assertFormula t

@[inherit_doc S.getLearnedLiterals]
def getLearnedLiterals (t : LearnedLitType := LearnedLitType.input) : Env Terms :=
  runUnsafe' do s.toUnsafe.getLearnedLiterals t.toUnsafe



/-! ### Declarations and definitions -/

/-- Declares a function symbol named `symbol`, of domain `sorts` and codomain `sort`.

```smtlib
(declare-fun <symbol> ( <sort>* ) <sort>)
```

A fresh symbol is declared by default. With `fresh := false`, a call with the same symbol and sorts
as an earlier non-fresh call answers the same term.
-/
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

/-- Defines a function named `symbol`, of parameters `bvs`, codomain `sort` and body `body`.

```smtlib
(define-fun <function_def>)
```

A `global` definition persists when the assertion stack is popped.
-/
def defineFun (symbol : String) (bvs : BVars) (sort : Srt) (body : Term)
  (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFun symbol bvs sort body global

/-- Defines a constant symbol as the given body. -/
def defineConst (symbol : String) (sort : Srt) (body : Term) (global : Bool := false) : Env Term :=
  s.defineFun symbol #[] sort body global

/-- Defines a function that may be recursive, named `symbol`, of parameters `bvs`, codomain `sort`.

The function does not exist before this call, so `body` cannot mention it; a self-referencing body
needs `defineFunRecTerm`. A `global` definition persists when the assertion stack is popped.

```smtlib
(define-fun-rec <function_def>)
```
-/
def defineFunRec (symbol : String) (bvs : BVars) (sort : Srt) (body : Term)
  (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFunRec symbol bvs sort body global

/-- Defines the recursive function `fn`, of parameters `bvs` and body `body`.

`fn` is a function symbol declared beforehand, with `declareFun` for instance, so `body` can mention
it. A `global` definition persists when the assertion stack is popped.

```smtlib
(define-fun-rec <function_def>)
```
-/
def defineFunRecTerm (fn : Term) (bvs : BVars) (body : Term) (global : Bool := false)
: Env Term :=
  runUnsafe' do s.toUnsafe.defineFunRecTerm fn bvs body global

/-- Defines mutually recursive functions: `funs[i]` has parameters `bvs[i]` and body `bodies[i]`.

Each function is a function symbol declared beforehand, with `declareFun` for instance. A `global`
definition persists when the assertion stack is popped.

```smtlib
(define-funs-rec ( <function_decl>* ) ( <body>* ))
```
-/
def defineFunsRec (funs : Terms) (bvs : Array BVars) (bodies : Terms)
  (global : Bool := false)
  (_oneBodyPerFun : funs.size = bodies.size := by
    (try grind) <;> fail "failed to prove there are as many bodies as functions")
  (_oneBvsPerBody : bvs.size = bodies.size := by
    (try grind) <;> fail "failed to prove there are as many bound-variable lists as bodies")
: Env Unit :=
  runUnsafe' do s.toUnsafe.defineFunsRec funs bvs bodies global



/-! ### Quantifier elimination, interpolants and abducts

Where cvc5 has no interpolant, abduct or disjunct to give, or an enumeration is exhausted, these
answer `none`. Each has a `!` form answering the term itself and failing there instead.
-/
-- cvc5 answers the null term in those cases; `none` stands for it, so that no null term ever
-- reaches a caller.

/-- `none` for the null term, the term itself otherwise. -/
private def nonNull? (t : cvc5.Term) : Option Term := if t.isNull then none else some t

/-- Quantifier elimination: a quantifier-free formula equivalent to `q` under the assertions.

Given the assertions `A`, the answer `Φ` is such that `A ∧ q` and `A ∧ Φ` are equivalent, and `Φ`
mentions only the free variables of `q`. Complete only for logics such as LRA, LIA and BV;
experimental in cvc5.

```smtlib
(get-qe <q>)
```
-/
def qe (q : Term) : Env Term := runUnsafe' do s.toUnsafe.getQuantifierElimination q

/-- Partial quantifier elimination, `none` if cvc5 answers the null term.

See `cvc5.Solver.getQuantifierEliminationDisjunct` for what the disjuncts are, and how repeated
calls compute the full elimination incrementally.
-/
def qeDisjunct (q : Term) : Env (Option Term) :=
  runUnsafe' do return nonNull? (← s.toUnsafe.getQuantifierEliminationDisjunct q)

/-- `qeDisjunct`, failing rather than answering `none`. -/
def qeDisjunct! (q : Term) : Env Term :=
  s.qeDisjunct q >>= someOrThrowUser s!"cvc5 answered no quantifier-elimination disjunct for `{q}`"

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

/-- `getInterpolant`, failing rather than answering `none`. -/
def getInterpolant! (conj : Term) (grammar : Option Grammar := none) : Env Term :=
  s.getInterpolant conj grammar
  >>= someOrThrowUser s!"cvc5 found no interpolant of the assertions and `{conj}`"

/-- The next interpolant, `none` when there is no other.

Only legal right after a successful `getInterpolant` or `getNextInterpolant`. Needs
`incremental`, which is on by default.
-/
def getNextInterpolant : Env (Option Term) :=
  runUnsafe' do return nonNull? (← s.toUnsafe.getInterpolantNext)

/-- `getNextInterpolant`, failing rather than answering `none`. -/
def getNextInterpolant! : Env Term :=
  s.getNextInterpolant >>= someOrThrowUser "cvc5 found no further interpolant"

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

/-- `getAbduct`, failing rather than answering `none`. -/
def getAbduct! (conj : Term) (grammar : Option Grammar := none) : Env Term :=
  s.getAbduct conj grammar
  >>= someOrThrowUser s!"cvc5 found no abduct of the assertions and `{conj}`"

/-- The next abduct, `none` when there is no other.

Only legal right after a successful `getAbduct` or `getNextAbduct`. Needs `incremental`, which
is on by default.
-/
def getNextAbduct : Env (Option Term) :=
  runUnsafe' do return nonNull? (← s.toUnsafe.getAbductNext)

/-- `getNextAbduct`, failing rather than answering `none`. -/
def getNextAbduct! : Env Term :=
  s.getNextAbduct >>= someOrThrowUser "cvc5 found no further abduct"



/-! ### Checking satisfiability -/

section check_sat variable (assuming : Option Terms := none)

/-- Checks the satisfiability of the assertions, and of `assuming` if given, as a raw result. -/
def checkSatResult : Env Result := do
  let code := if let some terms := assuming then S.checkSatAssuming s terms else S.checkSat s
  Result.ofUnsafe <$> runUnsafe' code

/-- Checks satisfiability: `.inl true` if sat, `.inl false` if unsat, `.inr why` if unknown. -/
def checkIsSat? : Env Result.Sat? := do (← s.checkSatResult assuming).isSat?

/-- Checks satisfiability, failing if the solver gives up. -/
def checkIsSat : Env Bool := do (← s.checkSatResult assuming).isSat

/-- Checks satisfiability, and runs the branch matching the answer.

Each branch runs in the monad of its answer, where the queries that answer allows can be written:

```lean
s.checkSat (ifSat := do println! "x = {← s.getValue x}") (ifUnsat := do println! "unsat")
```

A branch left out fails if its answer comes, with `unexpectedSat` and its siblings. `assuming`
checks under extra formulas, for this check only.
-/
def checkSat
  (ifSat : s.EnvSatT m α := s.unexpectedSat)
  (ifUnsat : s.EnvUnsatT m α := s.unexpectedUnsat)
  (ifUnknown : Unknown.Explanation → s.EnvUnknownT m α := liftM ∘ s.unexpectedUnknown)
: EnvT m α := do
  match ← s.checkIsSat? (assuming := assuming) with
  | .inl true => ifSat.toEnv
  | .inl false => ifUnsat.toEnv
  | .inr unkExpl => ifUnknown unkExpl |>.toEnv

/-- `checkSat` whose sat and unsat branches default to answering `none`.

A left-out unknown branch still fails.
-/
def checkSat? {α : Type} (s : Solver) (assuming : Option Terms := none)
  (ifSat : s.EnvSatT m (Option α) := return none)
  (ifUnsat : s.EnvUnsatT m (Option α) := return none)
  (ifUnknown : Unknown.Explanation → s.EnvUnknownT m (Option α) := liftM ∘ s.unexpectedUnknown)
: EnvT m (Option α) :=
  s.checkSat assuming ifSat ifUnsat ifUnknown

end check_sat



/-! ### Where the answer was sat -/

/-- The value of `term` in the model.

```smtlib
(get-value ( <term> ))
```
-/
def getValue (term : Term) : s.EnvSat Term := runUnsafe' do s.toUnsafe.getValue term

@[inherit_doc Cvc.Untyped.Solver.getValue]
abbrev _root_.Cvc.Untyped.Term.getValue {s: Solver} (term : Term) : s.EnvSat Term := s.getValue term

/-- The values of `terms` in the model.

```smtlib
(get-value ( <term>* ))
```
-/
def getValues (terms : Terms) : s.EnvSat Terms := runUnsafe' do s.toUnsafe.getValues terms

/-- The value the model gives a term, as the Lean value `α` denotes. -/
def getValueAs (α : Type) [TermToValue α] (term : Term) : s.EnvSat α := do
  Term.extractValue (α := α) (← s.getValue term)

/-- The values the model gives some terms, as the Lean values `α` denotes. -/
def getValuesAs (α : Type) [TermToValue α] (terms : Terms) : s.EnvSat (Array α) := do
  (← s.getValues terms).mapM fun value => (Term.extractValue value : s.EnvSat α)

/-- The elements of the uninterpreted sort `sort` in the model, which interprets it as finite. -/
def getModelDomainElements (sort : Srt) : s.EnvSat Terms :=
  runUnsafe' do s.toUnsafe.getModelDomainElements sort

/-- Whether the model value of the free constant `term` was essential for showing satisfiability.

Always `true` unless the `model-cores` option is set. Experimental in cvc5.
-/
def isModelCoreSymbol (term : Term) : s.EnvSat Bool :=
  runUnsafe' do s.toUnsafe.isModelCoreSymbol term

/-- The model, printed as SMT-LIB, over the uninterpreted sorts `sorts` and free constants `consts`.

A subset of `consts` may be printed, depending on `isModelCoreSymbol`. Needs `produce-models`;
experimental in cvc5.

```smtlib
(get-model)
```
-/
def getModelAsString (sorts : Srts) (consts : Terms) : s.EnvSat String :=
  runUnsafe' do s.toUnsafe.getModel sorts consts

/-- Blocks the current model, as `mode` says, so that later checks look for another one.

Needs `produce-models`; experimental in cvc5.

```smtlib
(block-model)
```
-/
def blockModel (mode : Model.BlockMode) : s.EnvSat Unit :=
  runUnsafe' do s.toUnsafe.blockModel mode.toUnsafe

/-- Blocks the current model values of (at least) `terms`, so that later checks look for others.

Needs `produce-models`; experimental in cvc5.

```smtlib
(block-model-values ( <term>+ ))
```
-/
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

/-- The assumptions the unsat answer rests on, among those `checkSat` was given in `assuming`.

Needs `produce-unsat-assumptions`.

```smtlib
(get-unsat-assumptions)
```
-/
def getUnsatAssumptions : s.EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatAssumptions

/-- An unsat core: assertions, and assumptions of the check if any, that are unsatisfiable together.

Needs `produce-unsat-cores`. Unlike SMT-LIB, named and unnamed assertions are not told apart.

```smtlib
(get-unsat-core)
```
-/
def getUnsatCore : s.EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCore

@[inherit_doc S.getUnsatCoreLemmas]
def getUnsatCoreLemmas : s.EnvUnsat Terms := runUnsafe' do s.toUnsafe.getUnsatCoreLemmas

/-- The proofs of the unsat answer for the component `pc`: the whole refutation by default.

`full` answers one proof; the other components may answer several, one per lemma for instance.
Needs `produce-proofs`; experimental in cvc5.

```smtlib
(get-proof :c)
```
-/
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

/-- A subset of the assertions that makes the solver time out, with the result of checking it.

Each internal check is limited by the `timeout-core-timeout` option. On an unknown result caused by
a timeout, the assertions are a timeout core; on an unsat result, an unsat core; on a sat result,
the assertions are satisfiable and the core is empty. Experimental in cvc5.

```smtlib
(get-timeout-core)
```
-/
def getTimeoutCore : s.EnvUnknown (Result × Terms) := runUnsafe' do
  let (res, terms) ← s.toUnsafe.getTimeoutCore
  return (Result.ofUnsafe res, terms)

/-- A subset of `assumptions` that makes the solver time out when added to the assertions.

Each internal check is limited by the `timeout-core-timeout` option. On an unknown result caused by
a timeout, the assumptions answered are a timeout core; on an unsat result, they form an unsat core
together with the assertions; on a sat result, the core is empty. Experimental in cvc5.

```smtlib
(get-timeout-core (<assert>*))
```
-/
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

/-- The proof rule used by the root step of the proof. -/
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

Takes as a hypothesis that `getRule` is `ProofRule.DSL_REWRITE` or `ProofRule.THEORY_REWRITE`,
which matching on `getRule` supplies:

```lean
match h : p.getRule with
| .DSL_REWRITE => some (p.getRewriteRule (.inl h))
| .THEORY_REWRITE => some (p.getRewriteRule (.inr h))
| _ => none
```
-/
def getRewriteRule : p.getRule = .DSL_REWRITE ∨ p.getRule = .THEORY_REWRITE → ProofRewriteRule :=
  𝕂 cvc5.Proof.getRewriteRule! p

/-- String representation, in `Proof.Format.no`. -/
def toString : Env String := Env.lift5 <| cvc5.Solver.proofToString solver p .NONE

/-- String representation in the given format.

Any format but `.no` needs a `full` proof; the obligation is discharged automatically when the
format and the component are both literals.
-/
def toStringFmt (fmt : Proof.Format := default)
: (valid : fmt = .no ∨ pc = .full := by grind) → Env String :=
  𝕂 Env.lift5 <| cvc5.Solver.proofToString solver p fmt.toUnsafe
-- cvc5 takes the process down when printing a non-`full` proof in a real format, hence a type
-- obligation rather than a runtime check.

end Proof

end Solver
