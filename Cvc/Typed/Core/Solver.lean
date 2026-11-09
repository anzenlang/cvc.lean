/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs
import all Cvc.Untyped.Core.Solver

public import Cvc.Untyped.Core.Solver
public import Cvc.Typed.Core.BVar
public import Cvc.Typed.Core.Bool



/-! # The solver, typed

A solver is the same object in both layers, so the functions mentioning no term — `s.setOption`,
`s.push`, `s.declareSrt`, … — are shared, and those below take and answer typed terms.

```lean
let s ← Solver.new
s.setOption "produce-models" "true"
let x ← s.declareConstAs Int "x"
s.assert (← smt! x + x = 6)
s.checkSat (ifSat := s.getValue x)   -- 3
```

`checkSat` runs one branch per answer, each in a monad allowing only the queries that answer makes
meaningful — `getValue` after sat, `getUnsatCore` after unsat — and only on the solver that
answered. Each such query also has a `!` twin in `Env`, which skips that check.
-/
-- Two kinds of name are restated here although `Solver` is the sort-erased type: those that must
-- be *spelled* in a signature (the mode monads, the result type), and `new`, which has no solver to
-- dot on.
namespace Cvc.Typed public section

/-- A solver instance. -/
abbrev Solver [Ω] := Cvc.Untyped.Solver

/-- A proof produced by solver `s` for component `pc`, whose conclusions are formulas, `Term Bool`.

The same cvc5 proof as the sort-erased `Cvc.Untyped.Solver.Proof`, under a type of its own: the
sort-erased functions do not accept it, and `toUntyped` (or `relax`) and `toTyped` cross for free.
-/
def Solver.Proof [Ω] (s : Solver) (pc : Proof.Component) : Type := Untyped.Solver.Proof s pc
-- A type of its own rather than an abbreviation, unlike `Solver`: an abbreviation unfolds, and
-- wherever this layer lacked a function, dot notation would then find the sort-erased one and
-- answer sort-erased terms, silently.

/-- The sort-erased solver it is, for free: the two layers share one solver type. -/
abbrev Solver.toUntyped [Ω] : Solver → Untyped.Solver := id

@[inherit_doc Solver.toUntyped]
abbrev Solver.relax [Ω] : Solver → Untyped.Solver := Solver.toUntyped

/-- The typed solver it is, for free: the two layers share one solver type. -/
abbrev _root_.Cvc.Untyped.Solver.toTyped [Ω] : Untyped.Solver → Solver := id

/-- The sort-erased proof it is, for free. -/
def Solver.Proof.toUntyped [Ω] {s : Solver}
: Solver.Proof s pc → Untyped.Solver.Proof s pc := id

@[inherit_doc Solver.Proof.toUntyped]
abbrev Solver.Proof.relax [Ω] {s : Solver} : Solver.Proof s pc → Untyped.Solver.Proof s pc :=
  Solver.Proof.toUntyped

/-- The typed proof it is, for free: a proof's conclusions are formulas whatever the layer. -/
def _root_.Cvc.Untyped.Solver.Proof.toTyped [Ω] {s : Untyped.Solver}
: Untyped.Solver.Proof s pc → Solver.Proof s pc := id

@[inherit_doc Untyped.Solver.Proof.instBEq]
instance Solver.Proof.instBEq [Ω] {s : Solver} : BEq (s.Proof pc) :=
  inferInstanceAs (BEq (Untyped.Solver.Proof s pc))

@[inherit_doc Untyped.Solver.Proof.instHashable]
instance Solver.Proof.instHashable [Ω] {s : Solver} : Hashable (s.Proof pc) :=
  inferInstanceAs (Hashable (Untyped.Solver.Proof s pc))

/-- An array of `Solver.Proof`. -/
abbrev Solver.Proofs [Ω] (s : Solver) (pc : Proof.Component) : Type := Array (Solver.Proof s pc)
-- Spelled `Array (Solver.Proof s)` rather than as an alias of `Untyped.Solver.Proofs`, following
-- `Terms`: the element type has to be *this* layer's, or taking an element out of the array — with
-- `for`, `map`, `getElem` — unfolds to the sort-erased head and the sort-erased accessors answer.

/-- A grammar generating terms of signature `σ`, built by `Solver.mkGrammar` or `smt.grammar!`.

It carries the parameters it was built over, so `synthFun` needs nothing else, and `σ` is those
parameters' sorts arrowed onto the start symbol's. Any solver of the scope accepts it.
-/
structure Grammar [Ω] (σ : Type) where
  private mk ::
  private untyped : Untyped.Grammar
-- Declared here rather than beside the builders in `Cvc.Typed.Grammar` because the interpolant and
-- abduct queries below take one.

/-- The sort-erased grammar it wraps, parameters and start sort included.

Free, and the two share one cvc5 grammar: a rule added through either shows in both, and once either
has been used by a solver, neither accepts more rules. `Untyped.Grammar.toTypedAs` goes back up.
-/
def Grammar.toUntyped [Ω] (g : Grammar σ) : Untyped.Grammar := g.untyped

@[inherit_doc Grammar.toUntyped]
abbrev Grammar.erase [Ω] (g : Grammar σ) : Untyped.Grammar := g.toUntyped

/-- String representation, as the SyGuS pre-declaration and rule set. -/
protected def Grammar.toString [Ω] (g : Grammar σ) : String := toString g.untyped

instance [Ω] : ToString (Grammar σ) := ⟨Grammar.toString⟩



/-- What a check-sat answered. -/
abbrev Result := Cvc.Untyped.Solver.Result

namespace Solver variable [Ω]

section variable (s : Solver) open Cvc.Untyped renaming Solver → S

@[inherit_doc S.EnvSatT] abbrev EnvSatT := S.EnvSatT s
@[inherit_doc S.EnvSat] abbrev EnvSat := S.EnvSat s
@[inherit_doc S.EnvUnsatT] abbrev EnvUnsatT := S.EnvUnsatT s
@[inherit_doc S.EnvUnsat] abbrev EnvUnsat := S.EnvUnsat s
@[inherit_doc S.EnvUnknownT] abbrev EnvUnknownT := S.EnvUnknownT s
@[inherit_doc S.EnvUnknown] abbrev EnvUnknown := S.EnvUnknown s

export Cvc.Untyped.Solver (EnvSatT EnvSat EnvUnsatT EnvUnsat EnvUnknownT EnvUnknown)



/-- Creates a new solver. -/
def new : Env Solver := Cvc.Untyped.Solver.new

section variable [Ω] [Monad m] [MonadLiftT BaseIO m] (s : Solver)


open Cvc renaming Untyped.Solver → U

/-- Declares a function symbol of type `α`, or a constant if `α` is not an arrow.

With `fresh := false`, declaring the same name at the same type again answers the same symbol.
-/
def declareFunAs (α : Type) (symbol : String) [ToTyp α] (fresh : Bool := true) : Env (Term α) := do
  let srt ← Srt.of α
  let domCod? : Option (Array Srt × Srt) := do
    let dom ← srt.getFunctionDomainSorts?
    let cod ← srt.getFunctionCodomainSort?
    pure (dom, cod)
  let (dom, cod) := if let some domCod := domCod? then domCod else (#[], srt)
  Untyped.Solver.declareFun s symbol dom cod (fresh := fresh)

@[inherit_doc declareFunAs]
abbrev declareFun [ToTyp α] (symbol : String) (fresh : Bool := true) : Env (Term α) :=
  s.declareFunAs α symbol (fresh := fresh)

/-- Defines a function symbol over bound variables `bvs` defined by `body`. -/
def defineFun [ToTyp β]
  (symbol : String) (bvs : BVars) (body : Term β)
: Env (Term (bvs.signatureTo β)) := do
  Untyped.Solver.defineFun s symbol bvs.erase (← Srt.of β) body

/-- Re-types a solver function, narrowing the terms it mentions.

The body is the sort-erased function unchanged: a typed term is definitionally its sort-erased
one, so narrowing an index is a matter of stating it.
-/
local macro "def% " id:ident sig:optDeclSig " ← " fnId:ident : command => do
  let fnId := ``U |>.append fnId.getId |> Lean.mkIdent
  `(@[inherit_doc $fnId] def $id $sig := $fnId)



/-! ## Assertions

An assertion is a formula, so these are the `Bool`-indexed terms.
-/

def% assert : (s : Solver) → (t : Term Bool) → Env Unit ← assert
def% getAssertions : (s : Solver) → Env (Terms Bool) ← getAssertions
-- a default argument does not survive the macro's eta-expansion, so these are spelled out
@[inherit_doc U.getLearnedLiterals]
def getLearnedLiterals (t : LearnedLitType := LearnedLitType.input) : Env (Terms Bool) :=
  U.getLearnedLiterals s t




/-! ## Quantifier elimination, interpolants and abducts -/

def% qe : (s : Solver) → (q : Term Bool) → Env (Term Bool) ← qe
def% qeDisjunct : (s : Solver) → (q : Term Bool) → Env (Option (Term Bool)) ← qeDisjunct
def% qeDisjunct! : (s : Solver) → (q : Term Bool) → Env (Term Bool) ← qeDisjunct!
@[inherit_doc U.getInterpolant]
def getInterpolant (conj : Term Bool) (grammar : Option (Grammar Bool) := none)
: Env (Option (Term Bool)) :=
  U.getInterpolant s conj (grammar.map Grammar.erase)
@[inherit_doc U.getInterpolant!]
def getInterpolant! (conj : Term Bool) (grammar : Option (Grammar Bool) := none)
: Env (Term Bool) :=
  U.getInterpolant! s conj (grammar.map Grammar.erase)
def% getNextInterpolant : (s : Solver) → Env (Option (Term Bool)) ← getNextInterpolant
def% getNextInterpolant! : (s : Solver) → Env (Term Bool) ← getNextInterpolant!
@[inherit_doc U.getAbduct]
def getAbduct (conj : Term Bool) (grammar : Option (Grammar Bool) := none)
: Env (Option (Term Bool)) :=
  U.getAbduct s conj (grammar.map Grammar.erase)
@[inherit_doc U.getAbduct!]
def getAbduct! (conj : Term Bool) (grammar : Option (Grammar Bool) := none)
: Env (Term Bool) :=
  U.getAbduct! s conj (grammar.map Grammar.erase)
def% getNextAbduct : (s : Solver) → Env (Option (Term Bool)) ← getNextAbduct
def% getNextAbduct! : (s : Solver) → Env (Term Bool) ← getNextAbduct!



/-! ## Declaring and defining symbols

The sort comes from the index, so these name a Lean type instead of a `Srt`; `fresh` is as for
`declareFun`.
-/

/-- Declares a constant of the sort `α` describes. -/
def declareConstAs (α : Type) [ToTyp α] (symbol : String) (fresh : Bool := true)
: Env (Term α) := do
  U.declareConst s symbol (← Srt.of α) fresh

/-- Declares a constant, its sort inferred from the expected type. -/
def declareConst [ToTyp α] (symbol : String) (fresh : Bool := true)
: Env (Term α) :=
  s.declareConstAs α symbol fresh

/-- Defines a constant as `body`, at `body`'s sort; `global` keeps it across `pop`. -/
def defineConst [ToTyp α] (symbol : String) (body : Term α) (global : Bool := false)
: Env (Term α) := do
  U.defineConst s symbol (← Srt.of α) body global



/-! ## Checking satisfiability -/

section check_sat variable (assuming : Option (Terms Bool) := none)

@[inherit_doc U.checkSatResult]
def checkSatResult : Env Result := U.checkSatResult s assuming

@[inherit_doc U.checkSatResult]
def checkIsSat? : Env Cvc.Untyped.Solver.Result.Sat? := U.checkIsSat? s assuming

@[inherit_doc U.checkSatResult]
def checkIsSat : Env Bool := U.checkIsSat s assuming

/-- Checks satisfiability, under `assuming` if given, and runs the branch for the answer.

`ifSat` runs in `s.EnvSat`, where the model can be read, `ifUnsat` in `s.EnvUnsat` (unsat cores,
proofs), `ifUnknown` on cvc5's explanation. An omitted branch throws if its answer comes up.
-/
def checkSat
  (ifSat : s.EnvSatT m α := s.unexpectedSat)
  (ifUnsat : s.EnvUnsatT m α := s.unexpectedUnsat)
  (ifUnknown : Unknown.Explanation → s.EnvUnknownT m α := liftM ∘ s.unexpectedUnknown)
: EnvT m α :=
  U.checkSat s assuming ifSat ifUnsat ifUnknown

/-- `checkSat`, whose sat and unsat branches default to `none`. -/
def checkSat? {α : Type} (s : Solver)
  (assuming : Option (Terms Bool) := none)
  (ifSat : s.EnvSatT m (Option α) := return none)
  (ifUnsat : s.EnvUnsatT m (Option α) := return none)
  (ifUnknown : Unknown.Explanation → s.EnvUnknownT m (Option α) := liftM ∘ s.unexpectedUnknown)
: EnvT m (Option α) :=
  U.checkSat? s assuming ifSat ifUnsat ifUnknown

end check_sat



/-! ## Where the answer was sat

Reading a value comes in two flavours: as a term still, or converted to the Lean value its index
describes.
-/

def% getValueTerm : (s : Solver) → (term : Term α) → s.EnvSat (Term α) ← getValue
def% getValueTerms : (s : Solver) → (terms : Terms α) → s.EnvSat (Terms α) ← getValues
def% isModelCoreSymbol : (s : Solver) → (term : Term α) → s.EnvSat Bool ← isModelCoreSymbol
def% blockModelValues : (s : Solver) → (terms : Terms α) → s.EnvSat Unit ← blockModelValues

/-- The value the model gives a term, as the Lean value its index describes. -/
def getValue [TermToValue α] (term : Term α) : s.EnvSat α := do
  let value ← s.getValueTerm term
  Term.extractValue value

@[inherit_doc getValue]
abbrev _root_.Cvc.Typed.Term.getValue [TermToValue α] {s : Solver} (term : Term α) : s.EnvSat α :=
  s.getValue term

@[inherit_doc getValueTerm]
abbrev _root_.Cvc.Typed.Term.getValueTerm [TermToValue α] {s : Solver} (term : Term α)
: s.EnvSat (Term α) :=
  s.getValueTerm term

/-- The values the model gives some terms, as the Lean values their index describes. -/
def getValues [TermToValue α] (terms : Terms α) : s.EnvSat (Array α) := do
  let values ← s.getValueTerms terms
  values.mapM fun value => (Term.getValue value : s.EnvSat α)

/-- The elements the model gives an uninterpreted sort. -/
def getModelDomainElements (α : Type) [ToTyp α] : s.EnvSat (Terms α) := do
  let srt ← (Srt.of α : Env Srt)
  U.getModelDomainElements s srt

def% getValueTerm! : (s : Solver) → (term : Term α) → Env (Term α) ← getValue!
def% getValueTerms! : (s : Solver) → (terms : Terms α) → Env (Terms α) ← getValues!
def% isModelCoreSymbol! : (s : Solver) → (term : Term α) → Env Bool ← isModelCoreSymbol!
def% blockModelValues! : (s : Solver) → (terms : Terms α) → Env Unit ← blockModelValues!

/-- `getValue` in `Env`, not checked to follow a sat answer. -/
def getValue! [TermToValue α] (term : Term α) : Env α := (s.getValue term).toEnv

/-- `getValue` in `Env`, not checked to follow a sat answer.

The solver is explicit, there being no expected mode monad to infer it from.
-/
abbrev _root_.Cvc.Typed.Term.getValueIn! [TermToValue α] (term : Term α) (s : Solver) : Env α :=
  s.getValue! term

/-- `getValues` in `Env`, not checked to follow a sat answer. -/
def getValues! [TermToValue α] (terms : Terms α) : Env (Array α) := (s.getValues terms).toEnv

/-- `getModelDomainElements` in `Env`, not checked to follow a sat answer. -/
def getModelDomainElements! (α : Type) [ToTyp α] : Env (Terms α) :=
  (s.getModelDomainElements α).toEnv



/-! ## Where the answer was unsat -/

def% getUnsatAssumptions : (s : Solver) → s.EnvUnsat (Terms Bool) ← getUnsatAssumptions
def% getUnsatCore : (s : Solver) → s.EnvUnsat (Terms Bool) ← getUnsatCore
def% getUnsatCoreLemmas : (s : Solver) → s.EnvUnsat (Terms Bool) ← getUnsatCoreLemmas

/-- The proof of the unsat answer this block stands on, for component `pc`.

Needs the solver option `produce-proofs`. The `full` component, the default, is the whole
refutation, and answers one proof; the others are its parts — preprocessing, the SAT solver's
reasoning, the theory lemmas — and may answer several, one per lemma for `theoryLemmas`. These are
this layer's proofs, whose conclusions are `Term Bool`.
-/
def getUnsatProof (pc : Proof.Component := Proof.Component.full) : s.EnvUnsat (s.Proofs pc) :=
  U.getUnsatProof s pc
-- Written out rather than stated with `def%`, twice over: the component argument has a default,
-- which eta-expansion would collapse, and the result has to be spelled at *this* layer's
-- `Proofs`, whose elements are this layer's `Solver.Proof`. The body is the sort-erased function
-- unchanged, a typed proof being a sort-erased one underneath.

def% getUnsatAssumptions! : (s : Solver) → Env (Terms Bool) ← getUnsatAssumptions!
def% getUnsatCore! : (s : Solver) → Env (Terms Bool) ← getUnsatCore!
def% getUnsatCoreLemmas! : (s : Solver) → Env (Terms Bool) ← getUnsatCoreLemmas!

/-- `getUnsatProof` in `Env`, not checked to follow an unsat answer. -/
def getUnsatProof! (pc : Proof.Component := Proof.Component.full) : Env (s.Proofs pc) :=
  (s.getUnsatProof pc).toEnv



/-! ## Where the answer was unknown -/

def% getTimeoutCore : (s : Solver) → s.EnvUnknown (Result × Terms Bool) ← getTimeoutCore
def% getTimeoutCoreAssuming :
  (s : Solver) → (assumptions : Terms Bool) → s.EnvUnknown (Result × Terms Bool)
← getTimeoutCoreAssuming

def% getTimeoutCore! : (s : Solver) → Env (Result × Terms Bool) ← getTimeoutCore!
def% getTimeoutCoreAssuming! :
  (s : Solver) → (assumptions : Terms Bool) → Env (Result × Terms Bool)
← getTimeoutCoreAssuming!

end

namespace Proof variable {solver : Solver} (p : solver.Proof pc)

@[inherit_doc Untyped.Solver.Proof.getRule]
def getRule : ProofRule := Untyped.Solver.Proof.getRule p

@[inherit_doc Untyped.Solver.Proof.getResult]
def getResult : Term Bool := Untyped.Solver.Proof.getResult p

@[inherit_doc Untyped.Solver.Proof.getArguments]
def getArguments : Untyped.Terms := Untyped.Solver.Proof.getArguments p

@[inherit_doc Untyped.Solver.Proof.getChildren]
def getChildren : solver.Proofs pc := Untyped.Solver.Proof.getChildren p

@[inherit_doc Untyped.Solver.Proof.getRewriteRule?]
def getRewriteRule? : Option ProofRewriteRule := Untyped.Solver.Proof.getRewriteRule? p

@[inherit_doc Untyped.Solver.Proof.getRewriteRule]
def getRewriteRule : p.getRule = .DSL_REWRITE ∨ p.getRule = .THEORY_REWRITE → ProofRewriteRule :=
  Untyped.Solver.Proof.getRewriteRule p

@[inherit_doc Untyped.Solver.Proof.toString]
def toString : Env String := Untyped.Solver.Proof.toString p

@[inherit_doc Untyped.Solver.Proof.toStringFmt]
def toStringFmt (fmt : Proof.Format := default) (valid : fmt = .no ∨ pc = .full := by grind)
: Env String :=
  Untyped.Solver.Proof.toStringFmt p fmt valid

end Proof

end

end Solver
