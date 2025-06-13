/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Lean.Server.Utils

import Cvc



namespace Cvc.Test

def IO.run : IO Unit → IO Unit :=
  id

def fail {α : outParam Type} (msg : String) : IO α :=
  IO.throwServerError msg

protected def pref (hint : String) : String :=
  if hint.isEmpty then "" else "[" ++ hint ++ "] "

def assertEq [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft != rgt then
    IO.eprintln s!"{Test.pref hint}comparison failed: `{lft}` is different from `{rgt}`"
    fail "assertion failed"

def assertNe [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft == rgt then
    IO.eprintln s!"{Test.pref hint}comparison failed: `{lft}` is the same as `{rgt}`"
    fail "assertion failed"


scoped syntax "show[" (str "| ")? (ident),+ "]" : term
macro_rules | `(show[ $[ $sep?:str | ]? $[ $idents:ident ],* ]) => do
  let sep := if let some sep := sep? then sep else Lean.Syntax.mkStrLit "\n"
  let data? ← idents.foldlM (init := none) fun acc? (ident : Lean.Syntax.Ident) => do
    let str := Lean.Syntax.mkStrLit ident.getId.toString
    let showIdent ← `($str ++ " ↦ " ++ toString $ident)
    if let some acc := acc?
    then `($acc ++ $sep ++ $showIdent)
    else pure showIdent
  if let some data := data?
  then `( IO.println ($data ++ "\n") )
  else `( IO.println "⁉️ nothing show ⁉️" )

/-- info:
n ↦ 5
n' ↦ 320
-/
#guard_msgs in #eval do
  let (n, n') := (5, 320)
  show[n, n']



scoped syntax ("Term.eval! " <|> "Smt.eval! ") term : command

open Lean.Parser.Term (doSeqIndent) in
scoped syntax (name := cvcTests) ("Term.test! " <|> "Smt.test! ")
  ( "with " doSeqIndent)?
  ( "[" declId "] " doSeqIndent docComment ? )+
: command

macro_rules
-- ideally errors should be reported at the position of `code`, currently they all appear at `test!`
-- top-level which is not ideal for series of tests
| `(command| Term.eval! $code:term) => `(#eval Cvc.Term.runIO ($code:term))
| `(command| Smt.eval! $code:term) => `(#eval Cvc.Smt.runIO ($code:term))

open Lean.Elab Command in
@[command_elab cvcTests]
def elabTests : CommandElab
| `(
  Term.test!
    $[ with $pref?:doSeqIndent ]?
    $[ [ $testId:ident ] $code:doSeqIndent $[ $outputComment:docComment ]? ]*
) => for (testId, code, outputComment) in testId.zip <| code.zip outputComment do
  try
    let codeElms ←
      match code with
      | `(Lean.Parser.Term.doSeqIndent| $[$codeItems:doSeqItem]*) =>
        if let some pref := pref? then
          match pref with
          | `(Lean.Parser.Term.doSeqIndent| $[$prefItems:doSeqItem]*) =>
            pure <| prefItems ++ codeItems
          | _ => throwUnsupportedSyntax
        else pure codeItems
      | _ => throwUnsupportedSyntax
    let guardedEval ← `(
      $[ $outputComment:docComment ]?
      #guard_msgs%$testId in Term.eval! do $[ $codeElms ]*
    )
    Lean.Elab.Command.elabCommand guardedEval
  catch exc => Lean.logErrorAt testId exc.toMessageData
| `(
  Smt.test!
    $[ with $pref?:doSeqIndent ]?
    $[ [ $testId:ident ] $code:doSeqIndent $[ $outputComment:docComment ]? ]*
) => for (testId, code, outputComment) in testId.zip <| code.zip outputComment do
  try
    let codeElms ←
      match code with
      | `(Lean.Parser.Term.doSeqIndent| $[$codeItems:doSeqItem]*) =>
        if let some pref := pref? then
          match pref with
          | `(Lean.Parser.Term.doSeqIndent| $[$prefItems:doSeqItem]*) =>
            pure <| prefItems ++ codeItems
          | _ => throwUnsupportedSyntax
        else pure codeItems
      | _ => throwUnsupportedSyntax
    let guardedEval ← `(
      $[ $outputComment:docComment ]?
      #guard_msgs%$testId in Smt.eval! do $[ $codeElms ]*
    )
    Lean.Elab.Command.elabCommand guardedEval
  catch exc => Lean.logErrorAt testId exc.toMessageData
| _ => Lean.Elab.throwUnsupportedSyntax


-- # Commented tests for debugging-QoL

-- Term.eval! do
--   let b1 ← Term.bool true
--   let b2 ← Term.bool false
--   Term.mkAdd #[b1, b2]

-- Smt.eval! do
--   let b1 ← Term.bool true
--   let b2 ← Term.bool false
--   Term.mkAdd #[b1, b2]

-- Smt.test!
-- [Term.mkAdd.nonArith] do
--   let b1 ← Term.bool true
--   let b2 ← Term.bool false
--   Term.mkAdd #[b1, b2]
-- /--
-- error: could not synthesize default value for parameter 'h_arith' using tactics
-- ---
-- error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
-- b1 b2 : Term.Bool
-- ⊢ Cvc.is_arith Bool
-- -/

-- Term.test! [Term.mkAdd.nonArith] do
--   let b1 ← Term.bool true
--   let b2 ← Term.bool false
--   Term.mkAdd #[b1, b2]
-- /--
-- error: could not synthesize default value for parameter 'h_arith' using tactics
-- ---
-- error: arithmetic type `Int` or `Rat` required, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
-- b1 b2 : Term.Bool
-- ⊢ Cvc.is_arith Bool
-- -/
