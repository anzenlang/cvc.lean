/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Symbols.Defs



/-! # Syntax extension for `Cvc.Symbols` (`Cvc.Symbol` structures)

## TODO

- support `extends Sub` as long as as a `Symbols Sub` instance can be found
-/
namespace Cvc.Symbols.Dsl



/-
Illustration of what elaboration should generate on a concrete example, used for testing/debugging
generation patterns.
-/

-- structure Testing.MySymbols (F : Symbol.Repr) where
--   s1 : F Int
--   s2 : F Bool

-- namespace Testing.MySymbols

-- @[default_instance]
-- instance inst : Symbols (fun F => MySymbols F) where
--   mapM self f := do
--     let s1 ← f self.s1
--     let s2 ← f self.s2
--     return mk s1 s2
--   forIn self acc f := do
--     let mut acc := acc
--     match ← f self.s1 acc with
--     | .done res => return res
--     | .yield acc' => acc := acc'
--     match ← f self.s2 acc with
--     | .done res => return res
--     | .yield acc' => acc := acc'
--     return acc

--   idents' := mk (Symbol.mkIdent "s1") (Symbol.mkIdent "s2")

-- abbrev Idents := inst.Idents
-- -- ...

-- def s1! (self : MySymbols (Symbol R ·)) := self.s1
-- def s2! (self : MySymbols (Symbol R ·)) := self.s2

-- end Testing.MySymbols



open Lean.Parser
open Command
open Lean.Elab.Command (elabCommand)

def symbolTk := leading_parser (nonReservedSymbol "symbol " true)

def symbolStructure := leading_parser
  ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
  optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)

scoped syntax (name := symbolStructureSyntax)
  declModifiers symbolTk structureTk declId symbolStructure
    -- Lean.Parser.Command.«structure»
: command

namespace Idents
def id_R := Lean.mkIdent `R
def id_inst := Lean.mkIdent `instSymbols
def id_Spec := Lean.mkIdent `Spec
def id_toSymbols := Lean.mkIdent `toSymbols
def id_Idents := Lean.mkIdent `Idents
def id_idents := Lean.mkIdent `idents
def id_Vals := Lean.mkIdent `Vals
def id_Model := Lean.mkIdent `Model
def id_Terms := Lean.mkIdent `Terms
def id_Fun := Lean.mkIdent `Fun
def id_Function := Lean.mkIdent `Function
def id_Pred := Lean.mkIdent `Pred
def id_Predicate := Lean.mkIdent `Predicate
def id_Rel := Lean.mkIdent `Rel
def id_Relation := Lean.mkIdent `Relation

def idRef_Symbol := Lean.mkIdent ``Cvc.Symbol
def idRef_Repr := Lean.mkIdent ``Cvc.Symbol.Repr
def idRef_Symbol_mkIdent := Lean.mkIdent ``Cvc.Symbol.mkIdent
def idRef_Symbols := Lean.mkIdent ``Cvc.Symbols
end Idents

open Idents in
@[command_elab symbolStructureSyntax]
def elabStateStructureSyntax : Lean.Elab.Command.CommandElab
| `(
  $topMods:declModifiers
  symbol structure $Symbols:ident where $[ $ctor:structCtor ]?
    $[ $fieldMods:declModifiers $fieldIdents:ident : $fieldTypes ]*
) => do
  let mut typs := #[]
  let mut ident'Elms := #[]
  let mut fieldIdentsBang := #[]
  for (fieldIdent, fieldType) in fieldIdents.zip fieldTypes do
    -- let typStx ← `( $idRef_Symbol ($fieldType) ($id_R ($fieldType)) $id_k)
    let typStx ← `( $(id_R) ($fieldType) )
    typs := typs.push typStx
    let identStr := fieldIdent.getId.toString
    let identStrLit := Lean.Syntax.mkStrLit identStr
    let ident'Elm ← `( $idRef_Symbol_mkIdent $identStrLit )
    ident'Elms := ident'Elms.push ident'Elm
    fieldIdentsBang :=
      identStr ++ "!" |> Lean.Name.mkSimple |> Lean.mkIdent |> fieldIdentsBang.push
  let stx ← `(
    $topMods:declModifiers
    structure $Symbols ( $id_R : $idRef_Repr )
    where $[ $ctor:structCtor ]?
      $[ $fieldMods:declModifiers $fieldIdents:ident : $typs ]*

    namespace $Symbols

    @[default_instance]
    instance $(id_inst):declId : $(idRef_Symbols) $Symbols where
      mapM (self : $Symbols _) f := do
        let ⟨ $[ $fieldIdents:ident ],*⟩ := self
        return ⟨ $[ ← f $fieldIdents:ident ],* ⟩
      forIn self acc f :=
        do
        let mut acc := acc
        $[
          match ← f self.$fieldIdents acc with
          | .yield newAcc => acc := newAcc
          | .done res => return res
        ]*
        return acc
      idents' := ⟨ $[ $ident'Elms ],* ⟩

    abbrev $id_toSymbols := $id_inst
    abbrev $id_Spec := $id_inst


    abbrev $id_Idents := $id_inst.$id_Idents
    abbrev $id_idents : $id_Idents := $id_inst.$id_idents
    abbrev $id_Vals := $id_inst.$id_Vals
    abbrev $id_Model := $id_Vals
    abbrev $id_Terms := $id_inst.$id_Terms
    protected abbrev $id_Fun := $id_inst.$id_Fun
    protected abbrev $id_Function := $id_inst.$id_Function
    abbrev $id_Pred := $id_inst.$id_Pred
    abbrev $id_Predicate := $id_Pred
    abbrev $id_Rel := $id_inst.$id_Rel
    abbrev $id_Relation := $id_Rel

    end $Symbols
  )
  elabCommand stx

  for (id!, id, typ) in fieldIdentsBang.zip <| fieldIdents.zip fieldTypes do
    let stx ← `(
      namespace $Symbols
      def $id! {R : $idRef_Repr} {β} [Get : Symbol.Getter (R $typ) β] (self : $Symbols R) : β :=
        Get.getInner self.$id
      end $Symbols
    )
    elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax



/-
More commented testing stuff.
-/
namespace Test

/-- Testing... -/
symbol structure MySymbols where
  myCounter : Int
  myReset : Bool

/-- info: Cvc.Symbols.Dsl.Test.MySymbols.Idents : Type -/
#guard_msgs in #check MySymbols.Idents

/-- info: Cvc.Symbols.Dsl.Test.MySymbols.idents : MySymbols.Idents -/
#guard_msgs in #check MySymbols.idents

/-- info: MySymbols.idents.myCounter : Symbol.Ident Int -/
#guard_msgs in #check MySymbols.idents.myCounter
/-- info: myCounter -/
#guard_msgs in #eval MySymbols.idents.myCounter
/-- info: MySymbols.myCounter! MySymbols.idents : String -/
#guard_msgs in #check MySymbols.idents.myCounter!
/-- info: "myCounter" -/
#guard_msgs in #eval MySymbols.idents.myCounter!

/-- info: MySymbols.idents.myReset : Symbol.Ident Bool -/
#guard_msgs in #check MySymbols.idents.myReset
/-- info: myReset -/
#guard_msgs in #eval MySymbols.idents.myReset
/-- info: MySymbols.myReset! MySymbols.idents : String -/
#guard_msgs in #check MySymbols.idents.myReset!
/-- info: "myReset" -/
#guard_msgs in #eval MySymbols.idents.myReset!

end Test

end Symbols.Dsl
