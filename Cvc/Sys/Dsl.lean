/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.State.Dsl
import Cvc.Sys.Defs



namespace Cvc.Sys.Dsl



open Lean.Parser
open Command
open Term (whereDecls)
open Lean.Elab.Command (elabCommand)

open scoped Cvc.State.Dsl


/- Drafting the syntax...

/-- doc -/
system MySys
with -- `with`-clause optional
  /-- doc -/
  state structure MyState where
    s1 : Int
    s2 : Bool
where
  State := MyState -- optional if `with`-clause present
  init state := smt! state.s1 = 0
  step prev curr := smt!
    curr.s1 = if curr.s2 then prev.s1 + 1 else prev.s1
    ∧ s2 = ¬ s2
  candidates := #[ ... ] -- optional, can add candidates later

-/

def systemTk := leading_parser (nonReservedSymbol "system " true)
def StateTk := leading_parser (nonReservedSymbol "State " true)
def initTk := leading_parser (nonReservedSymbol "init " true)
def stepTk := leading_parser (nonReservedSymbol "step " true)
def candidatesTk := leading_parser (nonReservedSymbol "candidates " true)

open State.Dsl (stateStructureSyntax stateStructure)

namespace Idents
def idRef_Sys := Lean.mkIdent ``Cvc.Sys
end Idents

scoped syntax (name := systemDefSyntax)
  declModifiers systemTk ident
  ( (" with " ppIndent( stateStructureSyntax )) <|> (" for " term) )
  whereDecls
  -- " where " structFields
: command

open Idents in
@[command_elab systemDefSyntax]
def elabSystemDefSyntax : Lean.Elab.Command.CommandElab
| `(
  $mods:declModifiers
  system $System:ident for $State:term
  where $tail
) => do
  sorry
| `(
  $mods:declModifiers system $System:ident
  with $stateMods:declModifiers state structure $State:ident $stateStruct:stateStructure
  $tail:whereDecls
) => do
  let stx ← `($stateMods:declModifiers state structure $State $stateStruct)
  elabCommand stx
  let stx ← `(
    $mods:declModifiers system $System for $State $tail:whereDecls
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax
