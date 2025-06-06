/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.TermDsl
import Cvc.State.Dsl
import Cvc.Sys.Defs



namespace Cvc.Sys.Dsl



open Lean.Parser
open Command
open Term (whereDecls)
open Lean.Elab.Command (elabCommand)

open scoped Cvc.State.Dsl
open scoped Cvc.Term.Dsl


/- Drafting the syntax...

/-- doc -/
system MySys
-- `for`-clause **or** `with`-clause
for MyState
with
  /-- doc -/
  state structure MyState where
    s1 : Int
    s2 : Bool
where
  init state := smt! state.s1 = 0
  step prev curr := smt!
    curr.s1 = if curr.s2 then prev.s1 + 1 else prev.s1
    ∧ s2 = ¬ s2
  candidates := #[ ... ] -- optional, can add candidates later

-/

def systemTk := leading_parser (nonReservedSymbol "system " true)

open State.Dsl (stateStructureSyntax stateStructure)

namespace Idents
def id_State := Lean.mkIdent `State
def id_mk := Lean.mkIdent `mk
def id_init := Lean.mkIdent `init
def id_step := Lean.mkIdent `step
def id_candidates := Lean.mkIdent `namedCandidates

def idRef_Sys := Lean.mkIdent ``_root_.Cvc.Sys
def idRef_Sys_mk := Lean.mkIdent ``Cvc.Sys.mk
def idRef_Smt := Lean.mkIdent ``Cvc.Smt
end Idents

scoped syntax (name := systemForDefSyntax)
  declModifiers systemTk structureTk ident group(" for " term) ppLine whereDecls
: command

open Symbols.Dsl.Idents in
open Idents in
@[command_elab systemForDefSyntax]
def elabSystemForDefSyntax : Lean.Elab.Command.CommandElab
| `(
  $mods:declModifiers
  system structure $SystemIdent:ident for $StateTerm:term
  $tail:whereDecls
) => do
  let System_State := SystemIdent.getId.append id_State.getId |> Lean.mkIdent
  -- set `$System_State` to be `Symbols` instance, fail if none found
  let stx ← `(
    def $System_State : $idRef_Symbols $StateTerm := by
      exact inferInstance <;> fail "could not find `{$idRef_Symbols}` instance for state type"
  )
  elabCommand stx
  let stx ← `(
    $mods:declModifiers
    -- abbrev $SystemIdent : (depth : Nat := 0) → Type := $idRef_Sys $System_State
    abbrev $SystemIdent (depth : Nat := 0) : Type := $idRef_Sys $System_State depth

    namespace $SystemIdent
    /-- Constructor. -/
    def $id_mk : $SystemIdent 0 :=
      $idRef_Sys_mk $id_init $id_step $id_candidates
    $tail:whereDecls
    end $SystemIdent
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax

scoped syntax (name := systemWithDefSyntax)
  declModifiers systemTk structureTk ident
  group(" with " ppLine ppIndent(stateStructureSyntax))
  ppLine whereDecls
: command

open Symbols.Dsl.Idents in
open Idents in
@[command_elab systemWithDefSyntax]
def elabSystemWithDefSyntax : Lean.Elab.Command.CommandElab
| `(
  $mods:declModifiers system structure $System:ident
  with $stateMods:declModifiers state structure $StateIdent:ident $stateStruct:stateStructure
  $tail:whereDecls
) => do
  let stx ← `($stateMods:declModifiers state structure $StateIdent $stateStruct)
  elabCommand stx
  let stx ← `(
    $mods:declModifiers system structure $System for $StateIdent $tail:whereDecls
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax



/-! ## Testing -/
namespace Test

namespace For

/-- State structure. -/
state structure MyState where
  bVar : Bool
  intVar : Int

/-- `MyState`- System. -/
system structure MySys for MyState
where
  init : MyState.StatePred := smtPred! state => 0 ≤ state.intVar
  step : MyState.StateRel := smtRel! prev curr =>
    (curr.intVar = if curr.bVar then prev.intVar + 1 else prev.intVar)
    ∧ curr.bVar = ¬ prev.bVar
  namedCandidates := .empty

/-- info: Cvc.Sys.Dsl.Test.For.MySys.State : Symbols MyState -/
#guard_msgs in #check MySys.State

/-- info: Cvc.Sys.Dsl.Test.For.MySys : optParam Nat 0 → Type -/
#guard_msgs in #check MySys
/-- info: MySys : Type -/
#guard_msgs in #check MySys 0
/-- info: MySys 5 : Type -/
#guard_msgs in #check MySys 5

end For



namespace With

/-- `MyState`-system. -/
system structure MySys
with
  /-- State structure. -/
  state structure MyState where
    bVar : Bool
    intVar : Int
where
  init : MyState.StatePred := smtPred! state => 0 ≤ state.intVar
  step : MyState.StateRel := smtRel! prev curr =>
    (curr.intVar = if curr.bVar then prev.intVar + 1 else prev.intVar)
    ∧ curr.bVar = ¬ prev.bVar
  namedCandidates := .empty

/-- info: Cvc.Sys.Dsl.Test.With.MyState (R : Symbol.Repr) : Type -/
#guard_msgs in #check MyState

/-- info: Cvc.Sys.Dsl.Test.With.MySys.State : Symbols MyState -/
#guard_msgs in #check MySys.State

/-- info: Cvc.Sys.Dsl.Test.With.MySys : optParam Nat 0 → Type -/
#guard_msgs in #check MySys

end With
