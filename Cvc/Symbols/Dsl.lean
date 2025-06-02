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

def symbolTk := leading_parser
  (nonReservedSymbol "symbol " true)

def symbolStructure := leading_parser
  declId >>
  ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
  optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)

scoped syntax (name := symbolStructureSyntax)
  declModifiers symbolTk structureTk symbolStructure
    -- Lean.Parser.Command.«structure»
: command

@[command_elab symbolStructureSyntax]
def elabStateStructureSyntax : Lean.Elab.Command.CommandElab
| `(
  $topMods:declModifiers
  symbol structure $topDeclId:declId where $[ $ctor:structCtor ]?
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
  let ident_Spec := Lean.mkIdent `Spec
  let ident_toSymbols := Lean.mkIdent `toSymbols
  let ident_Idents := Lean.mkIdent `Idents
  let ident_IdentsAt := Lean.mkIdent `IdentsAt
  let ident_idents := Lean.mkIdent `idents
  let ident_unroll := Lean.mkIdent `unroll
  let ident_Values := Lean.mkIdent `Vals
  let ident_ValuesAt := Lean.mkIdent `ValsAt
  let ident_Concrete := Lean.mkIdent `Concrete
  let ident_Model := Lean.mkIdent `Model
  let ident_Concrete := Lean.mkIdent `Concrete
  let ident_ConcreteAt := Lean.mkIdent `ConcreteAt
  let ident_ModelAt := Lean.mkIdent `ModelAt
  let ident_Terms := Lean.mkIdent `Terms
  let ident_TermsAt := Lean.mkIdent `TermsAt
  let ident_Fun := Lean.mkIdent `Fun
  let ident_Function := Lean.mkIdent `Function
  let ident_Pred := Lean.mkIdent `Pred
  let ident_Predicate := Lean.mkIdent `Predicate
  let ident_Rel := Lean.mkIdent `Rel
  let ident_Relation := Lean.mkIdent `Relation

  let mut typs := #[]
  let mut ident'Elms := #[]
  let mut fieldIdentsBang := #[]
  for (fieldIdent, fieldType) in fieldIdents.zip fieldTypes do
    -- let typStx ← `( $ident_Symbol ($fieldType) ($ident_F ($fieldType)) $ident_k)
    let typStx ← `( $ident_F ($fieldType) )
    typs := typs.push typStx
    let identStr := fieldIdent.getId.toString
    let identStrLit := Lean.Syntax.mkStrLit identStr
    let ident'Elm ← `( $ident_Symbol_mkIdent $identStrLit )
    ident'Elms := ident'Elms.push ident'Elm
    fieldIdentsBang :=
      identStr ++ "!"
      |> Lean.Name.mkSimple
      |> Lean.mkIdent
      |> fieldIdentsBang.push
  let stx ← `(
    $topMods:declModifiers
    structure $topDeclId ( $ident_F : $ident_Repr )
    where $[ $ctor:structCtor ]?
      $[ $fieldMods:declModifiers $fieldIdents:ident : $typs ]*

    namespace $identTop

    @[default_instance]
    instance $ident_inst:declId : $ident_Symbols $identTop where
      mapM (self : $identTop _) f := do
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

    abbrev $ident_toSymbols := $ident_inst
    abbrev $ident_Spec := $ident_inst


    abbrev $ident_Idents := $ident_inst.$ident_Idents
    abbrev $ident_idents : $ident_Idents := $ident_inst.$ident_idents
    abbrev $ident_Values := $ident_inst.$ident_Values
    abbrev $ident_Concrete := $ident_Values
    abbrev $ident_Model := $ident_Values
    abbrev $ident_Terms := $ident_inst.$ident_Terms
    protected abbrev $ident_Fun := $ident_inst.$ident_Fun
    protected abbrev $ident_Function := $ident_inst.$ident_Function
    abbrev $ident_Pred := $ident_inst.$ident_Pred
    abbrev $ident_Predicate := $ident_Pred
    abbrev $ident_Rel := $ident_inst.$ident_Rel
    abbrev $ident_Relation := $ident_Rel

    end $identTop
  )
  elabCommand stx

  for (id!, id, typ) in fieldIdentsBang.zip <| fieldIdents.zip fieldTypes do
    let stx ← `(
      namespace $identTop
      def $id! {R : $ident_Repr} {β} [Get : Symbol.Getter (R $typ) β] (self : $identTop R) : β :=
        Get.getInner self.$id
      end $identTop
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
