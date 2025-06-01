/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Symbols.Dsl
import Cvc.Symbols.Unroll



/-! # Syntax extension for `Cvc.Symbols` specialized for unrolling -/
namespace Cvc.Symbols.Dsl



/-
Illustration of what elaboration should generate on a concrete example, used for testing/debugging
generation patterns.
-/



open Lean.Parser
open Command
open Lean.Elab.Command (elabCommand)

open scoped Cvc.Symbols.Dsl

def systemTk := leading_parser
  (symbol "system ")

def systemStructure := leading_parser
  declId >>
  ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
  optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)

scoped syntax (name := systemStructureSyntax)
  declModifiers systemTk systemStructure
    -- Lean.Parser.Command.«structure»
: command

@[command_elab systemStructureSyntax]
def elabSystemStructureSyntax : Lean.Elab.Command.CommandElab
| `(
  $topMods:declModifiers
  system $topDeclId:declId where $[ $ctor:structCtor ]?
    $[ $fieldMods:declModifiers $fieldIdents:ident : $fieldTypes ]*
) => do
  let `( $identTop:ident ) := topDeclId.raw[0]
    | Lean.Elab.throwUnsupportedSyntax
  let ident_F := Lean.mkIdent `F
  let ident_Symbol := Lean.mkIdent ``Cvc.Symbol
  let ident_get := Lean.mkIdent `get
  let ident_Repr := Lean.mkIdent ``Cvc.Symbol.Repr
  let ident_Symbol_mkIdent := Lean.mkIdent ``Cvc.Symbol.mkIdent
  let ident_Symbols := Lean.mkIdent ``Cvc.Symbols
  let ident_inst := Lean.mkIdent `instSymbols
  let ident_Idents := Lean.mkIdent `Idents
  let ident_IdentsAt := Lean.mkIdent `IdentsAt
  let ident_idents := Lean.mkIdent `idents
  let ident_unroll := Lean.mkIdent `unroll
  let ident_ValsAt := Lean.mkIdent `ValsAt
  let ident_ConcreteAt := Lean.mkIdent `ConcreteAt
  let ident_ModelAt := Lean.mkIdent `ModelAt
  let ident_TermsAt := Lean.mkIdent `TermsAt

  let ident_FunAt := Lean.mkIdent `FunAt
  let ident_FunctionAt := Lean.mkIdent `FunctionAt
  let ident_PredAt := Lean.mkIdent `PredAt
  let ident_PredicateAt := Lean.mkIdent `PredicateAt
  let ident_RelAt := Lean.mkIdent `RelAt
  let ident_RelationAt := Lean.mkIdent `RelationAt
  let ident_InvRelAt := Lean.mkIdent `InvRelAt
  let ident_InvRelationAt := Lean.mkIdent `InvRelationAt

  let ident_unroll := Lean.mkIdent `unroll
  let ident_next := Lean.mkIdent `next
  let ident_declareAt := Lean.mkIdent `declareAt

  let stx ← `(
    $topMods:declModifiers
    symbols $topDeclId:declId where $[ $ctor:structCtor ]?
      $[ $fieldMods:declModifiers $fieldIdents:ident : $fieldTypes ]*
  )
  elabCommand stx

  let stx ← `(
    namespace $identTop

    abbrev $ident_IdentsAt (k : Nat) := $(ident_inst).$ident_IdentsAt k
    abbrev $ident_TermsAt (k : Nat) := $(ident_inst).$ident_TermsAt k
    abbrev $ident_ValsAt (k : Nat) := $(ident_inst).$ident_ValsAt k
    abbrev $ident_ConcreteAt (k : Nat) := $ident_ValsAt k
    abbrev $ident_ModelAt (k : Nat) := $ident_ValsAt k

    abbrev $ident_unroll (idents : Idents) (k : Nat := 0) : $ident_IdentsAt k :=
      $(ident_inst).$ident_unroll idents k
    abbrev $ident_next {k} (idents : $ident_IdentsAt k) : $ident_IdentsAt k.succ :=
      $(ident_inst).$ident_next idents

    abbrev $ident_declareAt (idents : Idents) (k : Nat := 0) : Cvc.Smt ($ident_TermsAt k) :=
      $(ident_inst).$ident_declareAt idents k

    abbrev $ident_FunAt (k : Nat) := $(ident_inst).$ident_FunAt k
    abbrev $ident_FunctionAt (k : Nat) := $(ident_inst).$ident_FunctionAt k
    abbrev $ident_PredAt (k : Nat) := $(ident_inst).$ident_PredAt k
    abbrev $ident_PredicateAt (k : Nat) := $(ident_inst).$ident_PredicateAt k
    abbrev $ident_RelAt (k : Nat) := $(ident_inst).$ident_RelAt k
    abbrev $ident_RelationAt (k : Nat) := $(ident_inst).$ident_RelationAt k
    abbrev $ident_InvRelAt (k : Nat) := $(ident_inst).$ident_InvRelAt k
    abbrev $ident_InvRelationAt (k : Nat) := $(ident_inst).$ident_InvRelationAt k
    end $identTop
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax



/-
More commented testing stuff.
-/
namespace Test

/-- Testing... -/
system MySystems where
  myCounter : Int
  myReset : Bool

/-- info: Cvc.Symbols.Dsl.Test.MySystems.Idents : Type -/
#guard_msgs in #check MySystems.Idents

/-- info: Cvc.Symbols.Dsl.Test.MySystems.idents : MySystems.Idents -/
#guard_msgs in #check MySystems.idents

/-- info: MySystems.idents.myCounter : Symbol.Ident Int -/
#guard_msgs in #check MySystems.idents.myCounter
/-- info: myCounter -/
#guard_msgs in #eval MySystems.idents.myCounter
/-- info: MySystems.myCounter! MySystems.idents : String -/
#guard_msgs in #check MySystems.idents.myCounter!
/-- info: "myCounter" -/
#guard_msgs in #eval MySystems.idents.myCounter!

/-- info: MySystems.unroll MySystems.idents 5 : MySystems.IdentsAt 5 -/
#guard_msgs in #check MySystems.idents.unroll 5
/-- info: myReset_unrolled_at_5 -/
#guard_msgs in #eval MySystems.idents.unroll 5 |>.myReset
/-- info: "myReset_unrolled_at_5" -/
#guard_msgs in #eval MySystems.idents.unroll 5 |>.myReset!

end Test

end Symbols.Dsl
