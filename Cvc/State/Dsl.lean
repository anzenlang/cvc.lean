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

def stateTk := leading_parser (nonReservedSymbol "state ")

def stateStructure := leading_parser
  ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
  optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)

-- def stateStructureParser := leading_parser
--   declModifiersF >> (nonReservedSymbol "state ") >> structureTk >> declId >> stateStructure

scoped syntax (name := stateStructureSyntax)
  declModifiersF stateTk structureTk declId stateStructure
: command
  -- stateStructureParser : command

namespace Idents
def id_IdentsAt := Lean.mkIdent `IdentsAt
def id_ValuesAt := Lean.mkIdent `ValuesAt
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
def id_StatePred := Lean.mkIdent `StatePred
def id_StatePredicate := Lean.mkIdent `StatePredicate
def id_StateRel := Lean.mkIdent `StateRel
def id_StateRelation := Lean.mkIdent `StateRelation
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
    abbrev $id_ValuesAt (k : Nat) := $(id_inst).$id_ValuesAt k
    abbrev $id_ModelAt (k : Nat) := $(id_inst).$id_ModelAt k

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

    abbrev $id_StatePred := $(id_inst).$id_StatePred
    abbrev $id_StatePredicate := $(id_inst).$id_StatePredicate
    abbrev $id_StateRel := $(id_inst).$id_StateRel
    abbrev $id_StateRelation := $(id_inst).$id_StateRelation
    end $State
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax



/-! ## Testing -/
namespace Test

/-- Testing... -/
state structure MyState where
  myCounter : Int
  myReset : Bool

/-- info: Cvc.State.Dsl.Test.MyState.Idents : Type -/
#guard_msgs in #check MyState.Idents

/-- info: Cvc.State.Dsl.Test.MyState.idents : MyState.Idents -/
#guard_msgs in #check MyState.idents

/-- info: MyState.idents.myCounter : Symbol.Ident Int -/
#guard_msgs in #check MyState.idents.myCounter
/-- info: myCounter -/
#guard_msgs in #eval MyState.idents.myCounter
/-- info: MyState.myCounter! MyState.idents : String -/
#guard_msgs in #check MyState.idents.myCounter!
/-- info: "myCounter" -/
#guard_msgs in #eval MyState.idents.myCounter!

/-- info: Symbols.unroll MyState.idents 5 : Symbols.IdentsAt 5 -/
#guard_msgs in #check MyState.idents.unroll 5
/-- info: myReset_unrolled_at_5 -/
#guard_msgs in #eval MyState.idents.unroll 5 |>.myReset
/-- info: "myReset_unrolled_at_5" -/
#guard_msgs in #eval MyState.idents.unroll 5 |>.myReset!



/-- Testing names featuring `.`-separators. -/
state structure My.State where
  myCounter : Int
  myReset : Bool

/-- info: Cvc.State.Dsl.Test.My.State.instSymbols : Symbols My.State -/
#guard_msgs in #check My.State.instSymbols
