/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe.Symbols



/-! # Syntax extension for `Cvc.Safe.Symbols` (`Cvc.Safe.Symbol` structures)

## TODO

- support `extends Sub` as long as as a `Symbols Sub` instance can be found
-/
namespace Cvc.Safe.Symbols



/-
Illustration of what elaboration should generate on a concrete example, used for testing/debugging
generation patterns.
-/

-- structure MySymbols (F : Type → Type) where
--   s1 : Symbol F Int
--   s2 : Symbol F Bool

-- namespace MySymbols

-- @[default_instance]
-- instance inst.{u, v} : Symbols.{u, v} MySymbols where
--   mapM self f := do
--     let s1 ← f self.s1
--     let s2 ← f self.s2
--     return mk (.mk s1) (.mk s2)
--   forIn self acc f := do
--     let mut acc := acc
--     match ← f self.s1.untype acc with
--     | .done res => return res
--     | .yield acc' => acc := acc'
--     match ← f self.s2.untype acc with
--     | .done res => return res
--     | .yield acc' => acc := acc'
--     return acc

--   idents' := mk "s1" "s2"

-- abbrev Idents.{u, v} := inst.Idents.{u, v}
-- -- ...

-- def s1! (self : MySymbols F) := self.s1.get
-- def s2! (self : MySymbols F) := self.s2.get

-- end MySymbols



class abbrev C := Ord Int

open Lean.Parser
open Command
open Lean.Elab.Command (elabCommand)

def symbolTk := leading_parser
  (symbol "symbol ")

def stateStructure := leading_parser
  declId >>
  ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
  optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields)

scoped syntax (name := stateStructureSyntax)
  declModifiers symbolTk
    structureTk stateStructure
    -- Lean.Parser.Command.«structure»
: command

@[command_elab stateStructureSyntax]
def elabStateStructureSyntax : Lean.Elab.Command.CommandElab
| `(
  $topMods:declModifiers
  symbol structure $topDeclId:declId where $[ $ctor:structCtor ]?
    $[ $fieldMods:declModifiers $fieldIdents:ident : $fieldTypes ]*
) => do
  let `( $identTop:ident ) := topDeclId.raw[0]
    | Lean.Elab.throwUnsupportedSyntax
  let ident_F := Lean.mkIdent `F
  let ident_Symbol := Lean.mkIdent ``Cvc.Safe.Symbol
  let ident_get := Lean.mkIdent `get
  let ident_Symbols := Lean.mkIdent ``Cvc.Safe.Symbols
  let ident_inst := Lean.mkIdent `instSymbols
  let ident_Spec := Lean.mkIdent `Spec
  let ident_toSymbols := Lean.mkIdent `toSymbols
  let ident_Idents := Lean.mkIdent `Idents
  let ident_idents := Lean.mkIdent `idents
  let ident_Values := Lean.mkIdent `Values
  let ident_Concrete := Lean.mkIdent `Concrete
  let ident_Model := Lean.mkIdent `Model
  let ident_Terms := Lean.mkIdent `Terms
  let ident_Fun := Lean.mkIdent `Fun
  let ident_Function := Lean.mkIdent `Function
  let ident_Pred := Lean.mkIdent `Pred
  let ident_Predicate := Lean.mkIdent `Predicate
  let ident_Rel := Lean.mkIdent `Rel
  let ident_Relation := Lean.mkIdent `Relation

  let mut typs := #[]
  let mut fieldNameStrings := #[]
  let mut fieldIdentsBang := #[]
  for (fieldIdent, fieldType) in fieldIdents.zip fieldTypes do
    let typStx ← `( $ident_Symbol $ident_F ($fieldType))
    typs := typs.push typStx
    let identStr := fieldIdent.getId.toString
    fieldNameStrings := fieldNameStrings.push (Lean.Syntax.mkStrLit identStr)
    fieldIdentsBang :=
      identStr ++ "!"
      |> Lean.Name.mkSimple
      |> Lean.mkIdent
      |> fieldIdentsBang.push
  let stx ←  `(
    $topMods:declModifiers
    structure $topDeclId ( $ident_F : Type → Type ) where $[ $ctor:structCtor ]?
      $[ $fieldMods:declModifiers $fieldIdents:ident : $typs ]*

    namespace $identTop

    instance $ident_inst:declId : $ident_Symbols $identTop where
      mapM self f := do
        let ⟨ $[ $fieldIdents:ident ],*⟩ := self
        return ⟨ $[ ← f self.$fieldIdents:ident ],* ⟩
      forIn self acc f := do
        let mut acc := acc
        $[
          match ← f (self.$fieldIdents).untype acc with
          | .yield newAcc => acc := newAcc
          | .done res => return res
        ]*
        return acc
      idents' := ⟨ $[ $fieldNameStrings ],* ⟩

    abbrev $ident_toSymbols := $ident_inst
    abbrev $ident_Spec := $ident_inst


    abbrev $ident_Idents := $ident_inst.{0, 0}.$ident_Idents
    abbrev $ident_idents : $ident_Idents := $ident_inst.{0, 0}.$ident_idents
    abbrev $ident_Values := $ident_inst.{0, 0}.$ident_Values
    abbrev $ident_Concrete := $ident_Values
    abbrev $ident_Model := $ident_Values
    abbrev $ident_Terms := $ident_inst.{0, 0}.$ident_Terms
    protected abbrev $ident_Fun := $ident_inst.{0, 0}.$ident_Fun
    protected abbrev $ident_Function := $ident_inst.{0, 0}.$ident_Function
    abbrev $ident_Pred := $ident_inst.{0, 0}.$ident_Pred
    abbrev $ident_Predicate := $ident_Pred
    abbrev $ident_Rel := $ident_inst.{0, 0}.$ident_Rel
    abbrev $ident_Relation := $ident_Rel

    end $identTop
  )
  elabCommand stx

  for (id!, id) in fieldIdentsBang.zip fieldIdents do
    let stx ← `(
      namespace $identTop
      def $id! {F} (self : $identTop F) := self.$id.$ident_get
      end $identTop
    )
    elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax



/-
More commented testing stuff.
-/

-- /-- Testing... -/
-- symbol structure MySymbols where
--   myCounter : Int
--   myReset : Bool

-- #check MySymbols.Idents

-- #check MySymbols.idents

-- #check MySymbols.idents.myCounter
-- #eval MySymbols.idents.myCounter
-- #check MySymbols.idents.myCounter!
-- #eval MySymbols.idents.myCounter!

-- #check MySymbols.idents.myReset
-- #eval MySymbols.idents.myReset
-- #check MySymbols.idents.myReset!
-- #eval MySymbols.idents.myReset!

end Symbols
