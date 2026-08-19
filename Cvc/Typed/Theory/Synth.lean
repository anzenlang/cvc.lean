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
import all Cvc.Typed.Core.Defs
import all Cvc.Typed.BVar
import all Cvc.Typed.Theory.Grammar
import all Cvc.Untyped.Theory.Synth

public import Cvc.Untyped.Theory.Synth
public import Cvc.Typed.Theory.Grammar
public import Cvc.Typed.Solver



/-! # Syntax-guided synthesis, typed

`checkSynth` asks for a function satisfying its constraints for every input, and a `Grammar`
restricts that function's shape.

The grammar is what carries the typing here. A `Grammar σ` already knows the parameters it was
built over and the sort it starts at, so `synthFun` needs nothing but the grammar and answers a
`Term σ` — the parameters cannot disagree with the grammar because there is only one place they
came from. `synthAnyFun` is the unconstrained form, where the signature has to be given instead.
-/
namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Solver → U

/-- The outcome of a synthesis check. -/
abbrev SynthResult := Cvc.Untyped.SynthResult

namespace Solver open Cvc.Untyped renaming Solver → S variable (s : Solver)
@[inherit_doc S.EnvSolvedT] abbrev EnvSolvedT := S.EnvSolvedT s
@[inherit_doc S.EnvSolved] abbrev EnvSolved := S.EnvSolved s
@[inherit_doc S.EnvUnsolvableT] abbrev EnvUnsolvableT := S.EnvUnsolvableT s
@[inherit_doc S.EnvUnsolvable] abbrev EnvUnsolvable := S.EnvUnsolvable s
@[inherit_doc S.EnvSynthUnknownT] abbrev EnvSynthUnknownT := S.EnvSynthUnknownT s
@[inherit_doc S.EnvSynthUnknown] abbrev EnvSynthUnknown := S.EnvSynthUnknown s
end Solver

namespace Solver variable [Monad m] [MonadLiftT BaseIO m] (s : Solver)

/-- Declares a universally quantified variable of the sort `α` describes.

Takes its type explicitly, like `Solver.declareConst`.
-/
def declareSygusVar (α : Type) [ToTyp α] (symbol : String) : Env (Term α) := do
  U.declareSygusVar s symbol (← Srt.of α)

/-- Declares a function to synthesize, restricted to what `g` generates.

The grammar carries the parameters and the start sort, so its index *is* the signature of the
function this declares.
-/
def synthFun (symbol : String) (g : Grammar σ) : Env (Term σ) :=
  U.synthFun s symbol g.boundVars g.startSrt g.toUntyped

/-- Declares a function to synthesize, unrestricted.

The counterpart of `synthFun` with no grammar to take a signature from, so the parameters and the
codomain are given directly — folded into the result's index exactly as `Solver.defineFun` folds
its own.
-/
def synthAnyFun' (symbol : String) (boundVars : BVars) (α : Type) [ToTyp α]
: Env (Term (boundVars.signatureTo α)) := do
  U.synthFun s symbol boundVars.erase (← Srt.of α)

@[inherit_doc synthAnyFun']
abbrev synthAnyFun [ToTyp α] (symbol : String) (boundVars : BVars)
: Env (Term (boundVars.signatureTo α)) := s.synthAnyFun' symbol boundVars α

/-- Adds a formula the synthesized functions must satisfy. -/
def addSygusConstraint (t : Term Bool) : Env Unit := U.addSygusConstraint s t

@[inherit_doc addSygusConstraint]
def getSygusConstraints : Env (Terms Bool) := U.getSygusConstraints s

/-- Adds a formula the synthesized functions may assume. -/
def addSygusAssume (t : Term Bool) : Env Unit := U.addSygusAssume s t

@[inherit_doc addSygusAssume]
def getSygusAssumptions : Env (Terms Bool) := U.getSygusAssumptions s

/-- Constrains `inv` to be an inductive invariant of the transition system.

`pre` must imply `inv`, `inv` must be preserved by `trans`, and `inv` must imply `post`.

The four indices are independent here. `inv`, `pre` and `post` are predicates over a state and
`trans` one over two, but a state is an arbitrary number of variables, so the relationship between
the four signatures is not one an index can state. cvc5 checks it.
-/
def addSygusInvConstraint (inv : Term α) (pre : Term β) (trans : Term γ) (post : Term δ)
: Env Unit :=
  U.addSygusInvConstraint s inv pre trans post

/-- Tries to solve the synthesis conjecture, as a raw result. -/
def checkSynthResult : Env SynthResult := U.checkSynthResult s

/-- Tries to find *another* solution, as a raw result. -/
def checkSynthNextResult : Env SynthResult := U.checkSynthNextResult s

@[inherit_doc checkSynthResult]
def checkSynth
  (ifSolved : s.EnvSolvedT m α := s.unexpectedSolved)
  (ifUnsolvable : s.EnvUnsolvableT m α := s.unexpectedUnsolvable)
  (ifUnknown : s.EnvSynthUnknownT m α := s.unexpectedSynthUnknown)
: EnvT m α :=
  U.checkSynth s ifSolved ifUnsolvable ifUnknown

@[inherit_doc U.checkSynthNext]
def checkSynthNext
  (ifSolved : s.EnvSolvedT m α := s.unexpectedSolved)
  (ifUnsolvable : s.EnvUnsolvableT m α := s.unexpectedUnsolvable)
  (ifUnknown : s.EnvSynthUnknownT m α := s.unexpectedSynthUnknown)
: s.EnvSolvedT m α :=
  U.checkSynthNext s ifSolved ifUnsolvable ifUnknown

@[inherit_doc checkSynthResult]
def checkSynth? {α : Type} (s : Solver)
  (ifSolved : s.EnvSolvedT m (Option α) := return none)
  (ifUnsolvable : s.EnvUnsolvableT m (Option α) := return none)
  (ifUnknown : s.EnvSynthUnknownT m (Option α) := return none)
: EnvT m (Option α) :=
  U.checkSynth? s ifSolved ifUnsolvable ifUnknown

/-- The solution found for a synthesized function.

A solution has the signature of the function it solves for, so the index carries across.
-/
def getSynthSolution (fn : Term σ) : s.EnvSolved (Term σ) := U.getSynthSolution s fn

@[inherit_doc getSynthSolution]
def getSynthSolutions (fns : Terms σ) : s.EnvSolved (Terms σ) := U.getSynthSolutions s fns

/-- Enumerates a term of interest, rather than solving a conjecture.

The grammar says what may be enumerated, and its start sort is what comes back.
-/
def findSynth (target : Cvc.Synth.FindTarget) (g : Grammar σ) : Env (Term σ) :=
  U.findSynth s target g.toUntyped

/-- Enumerates a term of interest with no grammar to restrict it.

Sort-erased: without a grammar nothing says what sort the answer has.
`Untyped.Term.typeCheck` puts an index back on once you know.
-/
def findAnySynth (target : Cvc.Synth.FindTarget) : Env Untyped.Term := U.findSynth s target

/-- Enumerates the next term of interest.

Sort-erased for the same reason as `findAnySynth`: which enumeration this continues is solver
state, not something a signature sees.
-/
def findSynthNext : Env Untyped.Term := U.findSynthNext s

end Solver
