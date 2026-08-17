/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Untyped.Term.Defs
import all Cvc.Typed.Term.Defs
-- `import all` and not a plain `import`: a typed term is definitionally its sort-erased one, and
-- that is what lets these delegate, but a plain import keeps the index opaque
-- `import all` again: the lift from `EnvT` into a mode monad is private, so that arbitrary code
-- cannot be run where an answer is being relied on. Re-typing here is exactly the sanctioned use.
import all Cvc.Untyped.Solver
import all Cvc.Typed.Grammar

public import Cvc.Untyped.Solver
public import Cvc.Typed.Grammar
public import Cvc.Typed.Term
public import Cvc.Typed.BVar



/-! # The solver, typed

A solver is the same object whichever layer you drive it from, so `Solver` is an abbreviation
rather than a new type. What differs between the layers is only how precisely a function's
signature describes the terms it takes and returns, and a function mentioning no term does not
differ at all — those are inherited here rather than restated.

Because the two `Solver`s are the same type, dot notation on a typed solver already resolves to
the shared functions: `s.setOption`, `s.push`, `s.declareSrt` need no restating. Two kinds of name
do need it — those that must be *spelled* in a signature (the mode monads, the result type), and
`new`, which has no solver to dot on.
-/
namespace Cvc.Typed public section

/-- A solver instance. -/
abbrev Solver [Ω] := Cvc.Untyped.Solver

/-- What a check-sat answered. -/
abbrev Result := Cvc.Untyped.Solver.Result

export Cvc.Untyped (EnvSatT EnvSat EnvUnsatT EnvUnsat EnvUnknownT EnvUnknown)

namespace Solver variable [Ω]

/-- Creates a new solver. -/
def new : Env Solver := Cvc.Untyped.Solver.new

section variable [Ω] [Monad m] [MonadLiftT BaseIO m] (s : Solver)


open Cvc renaming Untyped.Solver → U

/-- Declares a function symbol of type `α`. -/
def declareFun' (symbol : String) (α : Type) [ToTyp α] : Env (Term α) := do
  let srt ← Srt.of α
  let domCod? : Option (Array Srt × Srt) := do
    let dom ← srt.getFunctionDomainSorts?
    let cod ← srt.getFunctionCodomainSort?
    pure (dom, cod)
  let (dom, cod) := if let some domCod := domCod? then domCod else (#[], srt)
  Untyped.Solver.declareFun s symbol dom cod

@[inherit_doc declareFun']
abbrev declareFun [ToTyp α] (symbol : String) : Env (Term α) := s.declareFun' symbol α

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



/-! ## Grammars

`mkGrammar` is here rather than in `Cvc/Typed/Grammar.lean` because it needs a solver, and
that module defines the type the solver's own signatures mention.
-/

/-- A grammar over the given parameters, starting at `start`.

`boundVars` are the parameters of the `synth-fun` this grammar will constrain; the resulting index
is the signature those parameters and `start`'s sort describe. `others` are further non-terminals
the rules may mention.
-/
def mkGrammar [ToTyp α] (boundVars : BVars) (start : NT α) (others : NTs := [])
: Env (Grammar (boundVars.signatureTo α)) := do
  let startSrt ← Srt.of α
  let untyped ← Untyped.Solver.mkGrammar s boundVars.erase start.erase others.erase
  return ⟨untyped, boundVars.erase, startSrt⟩



/-! ## Quantifier elimination, interpolants and abducts -/

def% qe : (s : Solver) → (q : Term Bool) → Env (Term Bool) ← qe
def% qeDisjunct : (s : Solver) → (q : Term Bool) → Env (Term Bool) ← qeDisjunct
@[inherit_doc U.getInterpolant]
def getInterpolant (conj : Term Bool) (grammar : Option (Grammar Bool) := none) : Env (Term Bool) :=
  U.getInterpolant s conj (grammar.map Grammar.toUntyped)
def% getNextInterpolant : (s : Solver) → Env (Term Bool) ← getNextInterpolant
@[inherit_doc U.getAbduct]
def getAbduct (conj : Term Bool) (grammar : Option (Grammar Bool) := none) : Env (Term Bool) :=
  U.getAbduct s conj (grammar.map Grammar.toUntyped)
def% getNextAbduct : (s : Solver) → Env (Term Bool) ← getNextAbduct



/-! ## Declaring and defining symbols

The sort comes from the index, so these name the Lean type instead of a `Srt`. A function symbol
is one of these too, at an arrow index.
-/

/-- Declares a symbol of the given sort. -/
def declareConst (α : Type) [ToTyp α] (symbol : String) (fresh : Bool := true)
: Env (Term α) := do
  U.declareConst s symbol (← Srt.of α) fresh

/-- Defines a symbol of the given sort as the given body. -/
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

@[inherit_doc U.checkSat]
def checkSat
  (ifSat : EnvSatT m α := s.unexpectedSat)
  (ifUnsat : EnvUnsatT m α := s.unexpectedUnsat)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m α := liftM ∘ s.unexpectedUnknown)
: EnvT m α :=
  U.checkSat s assuming ifSat ifUnsat ifUnknown

@[inherit_doc U.checkSat]
def checkSat? {α : Type} (s : Solver)
  (assuming : Option (Terms Bool) := none)
  (ifSat : EnvSatT m (Option α) := return none)
  (ifUnsat : EnvUnsatT m (Option α) := return none)
  (ifUnknown : Unknown.Explanation → EnvUnknownT m (Option α) := liftM ∘ s.unexpectedUnknown)
: EnvT m (Option α) :=
  U.checkSat? s assuming ifSat ifUnsat ifUnknown

end check_sat



/-! ## Where the answer was sat

Reading a value comes in two flavours: as a term still, or converted to the Lean value its index
describes.
-/

def% getValueTerm : (s : Solver) → (term : Term α) → EnvSat (Term α) ← getValue
def% getValueTerms : (s : Solver) → (terms : Terms α) → EnvSat (Terms α) ← getValues
def% isModelCoreSymbol : (s : Solver) → (term : Term α) → EnvSat Bool ← isModelCoreSymbol
def% blockModelValues : (s : Solver) → (terms : Terms α) → EnvSat Unit ← blockModelValues

/-- The value the model gives a term, as the Lean value its index describes. -/
def getValue [TermToValue α] (term : Term α) : EnvSat α := do
  let value ← s.getValueTerm term
  Term.getValue value

/-- The values the model gives some terms, as the Lean values their index describes. -/
def getValues [TermToValue α] (terms : Terms α) : EnvSat (Array α) := do
  let values ← s.getValueTerms terms
  values.mapM fun value => (Term.getValue value : EnvSat α)

/-- The elements the model gives an uninterpreted sort. -/
def getModelDomainElements (α : Type) [ToTyp α] : EnvSat (Terms α) := do
  let srt ← (Srt.of α : Env Srt)
  U.getModelDomainElements s srt



/-! ## Where the answer was unsat -/

def% getUnsatAssumptions : (s : Solver) → EnvUnsat (Terms Bool) ← getUnsatAssumptions
def% getUnsatCore : (s : Solver) → EnvUnsat (Terms Bool) ← getUnsatCore
def% getUnsatCoreLemmas : (s : Solver) → EnvUnsat (Terms Bool) ← getUnsatCoreLemmas



/-! ## Where the answer was unknown -/

def% getTimeoutCore : (s : Solver) → EnvUnknown (Result × Terms Bool) ← getTimeoutCore
def% getTimeoutCoreAssuming :
  (s : Solver) → (assumptions : Terms Bool) → EnvUnknown (Result × Terms Bool)
← getTimeoutCoreAssuming

end
