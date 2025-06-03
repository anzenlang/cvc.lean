/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Symbols.Dsl
import Cvc.State.Defs



/-! # Syntax extension for `Cvc.Symbols` specialized for unrolling -/
namespace Cvc.State.Dsl



open Lean.Parser
open Command
open Lean.Elab.Command (elabCommand)

open scoped Cvc.Symbols.Dsl

def stateTk := leading_parser (nonReservedSymbol "state " true)

def stateStructure := leading_parser
  ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
  optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)

scoped syntax (name := stateStructureSyntax)
  declModifiers stateTk structureTk declId stateStructure
    -- Lean.Parser.Command.«structure»
: command

namespace Idents
def id_IdentsAt := Lean.mkIdent `IdentsAt
def id_ValsAt := Lean.mkIdent `ValsAt
def id_ModelAt := Lean.mkIdent `ModelAt
def id_TermsAt := Lean.mkIdent `TermsAt
def id_FunAt := Lean.mkIdent `FunAt
def id_FunctionAt := Lean.mkIdent `FunctionAt
def id_PredAt := Lean.mkIdent `PredAt
def id_PredicateAt := Lean.mkIdent `PredicateAt
def id_RelAt := Lean.mkIdent `RelAt
def id_RelationAt := Lean.mkIdent `RelationAt
def id_InvRelAt := Lean.mkIdent `InvRelAt
def id_InvRelationAt := Lean.mkIdent `InvRelationAt
def id_unroll := Lean.mkIdent `unroll
def id_next := Lean.mkIdent `next
def id_declareAt := Lean.mkIdent `declareAt
end Idents

open Symbols.Dsl.Idents in
open Idents in
@[command_elab stateStructureSyntax]
def elabStateStructureSyntax : Lean.Elab.Command.CommandElab
| `(
  $topMods:declModifiers
  state structure $State:ident where $[ $ctor:structCtor ]?
    $[ $fieldMods:declModifiers $fieldIdents:ident : $fieldTypes ]*
) => do

  let stx ← `(
    $topMods:declModifiers
    symbol structure $State:declId where $[ $ctor:structCtor ]?
      $[ $fieldMods:declModifiers $fieldIdents:ident : $fieldTypes ]*
  )
  elabCommand stx

  let stx ← `(
    namespace $State

    abbrev $id_IdentsAt (k : Nat) := $(id_inst).$id_IdentsAt k
    abbrev $id_TermsAt (k : Nat) := $(id_inst).$id_TermsAt k
    abbrev $id_ValsAt (k : Nat) := $(id_inst).$id_ValsAt k
    abbrev $id_ModelAt (k : Nat) := $id_ValsAt k

    abbrev $id_unroll (idents : $id_Idents) (k : Nat := 0) : $id_IdentsAt k :=
      $(id_inst).$id_unroll idents k
    abbrev $id_next {k} (idents : $id_IdentsAt k) : $id_IdentsAt k.succ :=
      $(id_inst).$id_next idents

    abbrev $id_declareAt (idents : $id_Idents) (k : Nat := 0) : Cvc.Smt ($id_TermsAt k) :=
      $(id_inst).$id_declareAt idents k

    abbrev $id_FunAt (k : Nat) := $(id_inst).$id_FunAt k
    abbrev $id_FunctionAt (k : Nat) := $(id_inst).$id_FunctionAt k
    abbrev $id_PredAt (k : Nat) := $(id_inst).$id_PredAt k
    abbrev $id_PredicateAt (k : Nat) := $(id_inst).$id_PredicateAt k
    abbrev $id_RelAt (k : Nat) := $(id_inst).$id_RelAt k
    abbrev $id_RelationAt (k : Nat) := $(id_inst).$id_RelationAt k
    abbrev $id_InvRelAt (k : Nat) := $(id_inst).$id_InvRelAt k
    abbrev $id_InvRelationAt (k : Nat) := $(id_inst).$id_InvRelationAt k
    end $State
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax



/-
More commented testing stuff.
-/
namespace Test

/-- Testing... -/
state structure MySystems where
  myCounter : Int
  myReset : Bool

/-- info: Cvc.State.Dsl.Test.MySystems.Idents : Type -/
#guard_msgs in #check MySystems.Idents

/-- info: Cvc.State.Dsl.Test.MySystems.idents : MySystems.Idents -/
#guard_msgs in #check MySystems.idents

/-- info: MySystems.idents.myCounter : Symbol.Ident Int -/
#guard_msgs in #check MySystems.idents.myCounter
/-- info: myCounter -/
#guard_msgs in #eval MySystems.idents.myCounter
/-- info: MySystems.myCounter! MySystems.idents : String -/
#guard_msgs in #check MySystems.idents.myCounter!
/-- info: "myCounter" -/
#guard_msgs in #eval MySystems.idents.myCounter!

/-- info: Symbols.unroll MySystems.idents 5 : Symbols.IdentsAt 5 -/
#guard_msgs in #check MySystems.idents.unroll 5
/-- info: myReset_unrolled_at_5 -/
#guard_msgs in #eval MySystems.idents.unroll 5 |>.myReset
/-- info: "myReset_unrolled_at_5" -/
#guard_msgs in #eval MySystems.idents.unroll 5 |>.myReset!
