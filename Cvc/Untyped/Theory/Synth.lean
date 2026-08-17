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
import all Cvc.Untyped.Solver

public import Cvc.Basic
public import Cvc.Basic.Env
public import Cvc.Untyped.Mode
public import Cvc.Untyped.Theory.Grammar



/-! # Syntax-guided synthesis, sort-erased

Where `checkSat` asks whether constraints *can* be satisfied, `checkSynth` asks for a function that
satisfies them for every input. The shape of that function is what a `Grammar` restricts.

The pieces fit together in one order: declare the universally quantified variables with
`declareSygusVar`, declare the functions to synthesize with `synthFun`, constrain them with
`addSygusConstraint`, then `checkSynth` and read each function back with `getSynthSolution`.
`findSynth` is the other entry point — it enumerates terms of interest rather than solving a
conjecture.
-/
namespace Cvc.Untyped public section variable [Ω]



/-! ## Synthesis-mode monadic environments

A synthesis check splits the world in three, as a check-sat does, and the queries that make sense
differ in each: a solution can be read only where one was found. The `env_gen%` mechanism is the
same, and so is the guarantee — the lift from `EnvT` is private to this module, so only
`checkSynth` below can enter these.

They are separate from the sat monads on purpose. `EnvUnknown` gates a *timeout core*, which has
nothing to do with a synthesis check giving up, so reusing it would let one be asked for where it
does not exist.
-/
section variable [Ω] [Monad m]

/-- Code running where the solver last found a synthesis solution. -/
structure EnvSolvedT [Ω] (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvSolvedT / EnvSolved

/-- Code running where the solver last showed the synthesis conjecture has no solution. -/
structure EnvUnsolvableT (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvUnsolvableT / EnvUnsolvable

/-- Code running where the solver last gave up on a synthesis conjecture. -/
structure EnvSynthUnknownT (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvSynthUnknownT / EnvSynthUnknown

end



/-! ## What a synthesis check answered -/

/-- The outcome of a synthesis check. -/
def SynthResult := cvc5.SynthResult

namespace SynthResult

private def toUnsafe : SynthResult → cvc5.SynthResult := id
private def ofUnsafe : cvc5.SynthResult → SynthResult := id

section variable (r : SynthResult)

@[inherit_doc cvc5.SynthResult.toString]
protected def toString : String := r.toUnsafe.toString
instance : ToString SynthResult := ⟨SynthResult.toString⟩

@[inherit_doc cvc5.SynthResult.hasSolution]
def hasSolution : Bool := r.toUnsafe.hasSolution
@[inherit_doc cvc5.SynthResult.hasNoSolution]
def hasNoSolution : Bool := r.toUnsafe.hasNoSolution
@[inherit_doc cvc5.SynthResult.isUnknown]
def isUnknown : Bool := r.toUnsafe.isUnknown

/-- Whether a solution was found, or `none` if the solver could not tell.

The three-way answer of `Result.isSat?`, at synthesis: `some true` if a solution exists and was
found, `some false` if the conjecture has none, `none` if the solver gave up.
-/
def isSolved? : Res (Option Bool) :=
  if r.hasSolution then return some true
  else if r.hasNoSolution then return some false
  else if r.isUnknown then return none
  else throwInternal s!"synthesis result is none of solved, unsolvable or unknown\n{r}"

/-- Whether a solution was found, failing if the solver gave up. -/
def isSolved : Res Bool := r.isSolved? >>= fun
  | some solved => return solved
  | none => throwUser "unexpected unknown synthesis result"

end

end SynthResult



/-! ## Driving synthesis -/

namespace Solver variable [Monad m] [MonadLiftT BaseIO m] (s : Solver)

/-- Declares a universally quantified variable of the given sort. -/
def declareSygusVar (symbol : String) (srt : Srt) : Env Term :=
  runUnsafe' do s.toUnsafe.declareSygusVar symbol srt.toUnsafe

/-- Declares a function to synthesize.

`boundVars` are the function's parameters and `srt` its codomain. A `grammar` restricts the shape
of the candidates; without one, any term of the right sort is allowed. The grammar must have been
built over these very parameters.
-/
def synthFun (symbol : String) (boundVars : BVars) (srt : Srt)
  (grammar : Option Grammar := none)
: Env Term :=
  runUnsafe' do
    s.toUnsafe.synthFun symbol (boundVars.map BVar.toTerm) srt.toUnsafe grammar

/-- Adds a formula the synthesized functions must satisfy. -/
def addSygusConstraint (t : Term) : Env Unit :=
  runUnsafe' do s.toUnsafe.addSygusConstraint t

@[inherit_doc addSygusConstraint]
def getSygusConstraints : Env Terms :=
  runUnsafe' do s.toUnsafe.getSygusConstraints

/-- Adds a formula the synthesized functions may assume. -/
def addSygusAssume (t : Term) : Env Unit :=
  runUnsafe' do s.toUnsafe.addSygusAssume t

@[inherit_doc addSygusAssume]
def getSygusAssumptions : Env Terms :=
  runUnsafe' do s.toUnsafe.getSygusAssumptions

/-- Constrains `inv` to be an inductive invariant of the transition system.

`pre` must imply `inv`, `inv` must be preserved by `trans`, and `inv` must imply `post`.
-/
def addSygusInvConstraint (inv pre trans post : Term) : Env Unit :=
  runUnsafe' do s.toUnsafe.addSygusInvConstraint inv pre trans post

/-! ### Rejecting an unexpected answer

What a synthesis branch falls back on when the caller did not expect that answer. The analogue of
dumping the assertions is dumping the sygus constraints.
-/

section unexpected

/-- The sygus constraints, as SMT-LIB, for an error message. -/
private def constraintsForError : Env (Array String) := do
  let constraints ← runUnsafe' do s.toUnsafe.getSygusConstraints
  return constraints.map toString

private def unexpectedSynth (badResDesc : String) (dumpConstraints : Bool) : Env α := do
  let mut msg := s!"unexpected `{badResDesc}` synthesis result"
  if dumpConstraints then
    let constraints ← s.constraintsForError
    if constraints.isEmpty then
      msg := s!"{msg}, solver does not have any sygus constraints"
    else
      msg := msg ++ " for the following constraints\n```smtlib"
        |> constraints.foldl (s!"{·}\n(constraint {·})")
      msg := msg ++ "\n```"
  throwUser msg

variable (dumpConstraints : Bool := false)

/-- Fails because a solution was unexpected. -/
def unexpectedSolved : EnvSolved α := s.unexpectedSynth "solved" dumpConstraints
/-- Fails because having no solution was unexpected. -/
def unexpectedUnsolvable : EnvUnsolvable α := s.unexpectedSynth "unsolvable" dumpConstraints
/-- Fails because the solver giving up was unexpected. -/
def unexpectedSynthUnknown : EnvSynthUnknown α := s.unexpectedSynth "unknown" dumpConstraints

end unexpected



/-! ### Checking a synthesis conjecture

`checkSynth` is the only way into the synthesis-mode monads: it runs the branch matching the answer
the solver actually gave, and a branch the caller did not supply rejects that answer.
-/

/-- Tries to solve the synthesis conjecture, as a raw result. -/
def checkSynthResult : Env SynthResult :=
  SynthResult.ofUnsafe <$> runUnsafe' s.toUnsafe.checkSynth

/-- Tries to find *another* solution, as a raw result. -/
def checkSynthNextResult : Env SynthResult :=
  SynthResult.ofUnsafe <$> runUnsafe' s.toUnsafe.checkSynthNext

@[inherit_doc checkSynthResult]
def checkSynth
  (ifSolved : EnvSolvedT m α := s.unexpectedSolved)
  (ifUnsolvable : EnvUnsolvableT m α := s.unexpectedUnsolvable)
  (ifUnknown : EnvSynthUnknownT m α := s.unexpectedSynthUnknown)
: EnvT m α := do
  match ← (← s.checkSynthResult).isSolved? with
  | some true => ifSolved.toEnv
  | some false => ifUnsolvable.toEnv
  | none => ifUnknown.toEnv

/-- Tries to find *another* solution to the synthesis conjecture.

Only where one was already found, which is what `EnvSolved` records; the answer re-splits the
world, so this takes the same three branches `checkSynth` does.
-/
def checkSynthNext
  (ifSolved : EnvSolvedT m α := s.unexpectedSolved)
  (ifUnsolvable : EnvUnsolvableT m α := s.unexpectedUnsolvable)
  (ifUnknown : EnvSynthUnknownT m α := s.unexpectedSynthUnknown)
: EnvSolvedT m α := .wrap do
  match ← (← s.checkSynthNextResult).isSolved? with
  | some true => ifSolved.toEnv
  | some false => ifUnsolvable.toEnv
  | none => ifUnknown.toEnv

@[inherit_doc checkSynthResult]
def checkSynth? {α : Type} (s : Solver)
  (ifSolved : EnvSolvedT m (Option α) := return none)
  (ifUnsolvable : EnvUnsolvableT m (Option α) := return none)
  (ifUnknown : EnvSynthUnknownT m (Option α) := return none)
: EnvT m (Option α) :=
  s.checkSynth ifSolved ifUnsolvable ifUnknown



/-! ### Where a solution was found -/

/-- The solution found for a synthesized function. -/
def getSynthSolution (fn : Term) : EnvSolved Term :=
  runUnsafe' do s.toUnsafe.getSynthSolution fn

@[inherit_doc getSynthSolution]
def getSynthSolutions (fns : Terms) : EnvSolved Terms :=
  runUnsafe' do s.toUnsafe.getSynthSolutions fns

/-- Enumerates a term of interest, rather than solving a conjecture.

A `grammar` restricts what may be enumerated.
-/
def findSynth (target : Cvc.Synth.FindTarget) (grammar : Option Grammar := none) : Env Term :=
  runUnsafe' do s.toUnsafe.findSynth target.toUnsafe grammar

@[inherit_doc findSynth]
def findSynthNext : Env Term :=
  runUnsafe' do s.toUnsafe.findSynthNext

end Solver
