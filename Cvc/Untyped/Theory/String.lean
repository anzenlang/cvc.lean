/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

public import Cvc.Ext
public import Cvc.Gen.View
public import Cvc.Untyped.Core.View
public meta import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Gen.Term
public import Cvc.Spec.String



/-! # Generated String constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.String
gen_untyped_view% from Cvc.Spec.String



/-! ## Values -/

/-- Whether a term is a string value. -/
def isStringValue (term : Term) : Bool := T.isStringValue term.toUnsafe

/-- The value of a hexadecimal digit. -/
private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The number some hexadecimal digits write, if they are all digits. -/
private def hexValue? (digits : List Char) : Option Nat :=
  digits.foldlM (fun acc d => (acc * 16 + ·) <$> hexDigit? d) 0

/-- The characters an SMT-LIB string literal's contents stand for.

`""` is a quote, `\u{d}` (one to five hex digits) and `\udddd` a code point, and anything else
stands for itself.
-/
private partial def unescape : List Char → List Char
  | '"' :: '"' :: rest => '"' :: unescape rest
  | '\\' :: tl@('u' :: '{' :: rest) =>
    match rest.span (· != '}') with
    | (digits, '}' :: rest') =>
      match hexValue? digits with
      | some n => if 0 < digits.length ∧ digits.length ≤ 5 then Char.ofNat n :: unescape rest'
                  else '\\' :: unescape tl
      | none => '\\' :: unescape tl
    | _ => '\\' :: unescape tl
  | '\\' :: tl@('u' :: a :: b :: c :: d :: rest) =>
    match hexValue? [a, b, c, d] with
    | some n => Char.ofNat n :: unescape rest
    | none => '\\' :: unescape tl
  | c :: rest => c :: unescape rest
  | [] => []

/-- The string a term denotes, failing if it denotes none. -/
def getStringValue (term : Term) : Res String :=
  if term.isStringValue then
    let s := toString term
    if s.startsWith '"' ∧ s.endsWith '"' then
      return String.ofList (unescape (s.drop 1 |>.dropEnd 1 |>.toString).toList)
    else throwUser s!"failed to retrieve string value of term `{s}`"
  else throwUser "cannot extract the string value of a term that denotes no string"
-- lean-cvc5 does not expose cvc5's string-value accessor, so this reads the term's printed form,
-- the SMT-LIB string literal, and undoes its escapes.

/-- The string term denoting `s`, whatever characters it holds.

Fails on a character beyond cvc5's alphabet, whose code points stop at `0x2FFFF`.
-/
def mkStringValue (s : String) : Env Term := do
  let mut lit := ""
  for c in s.toList do
    let n := c.toNat
    if 32 ≤ n ∧ n ≤ 126 ∧ c ≠ '\\' then lit := lit.push c
    else if n ≤ 0x2FFFF then lit := lit ++ "\\u{" ++ String.ofList (Nat.toDigits 16 n) ++ "}"
    else
      let code := String.ofList (Nat.toDigits 16 n)
      throwUser s!"`{s}` holds U+{code}, beyond the characters cvc5 supports"
  mkString lit true
-- cvc5 takes printable ASCII as is but refuses any other character unescaped, so those, and the
-- backslash an escape starts with, are written as `\u{…}`.

@[inherit_doc getStringValue]
def getStringValue? (term : Term) : Option String := term.getStringValue.toOption

instance : SrtLike String where
  valueToTerm := mkStringValue
  termToValue t := t.getStringValue



/-! ## `smt!` literals

String literals in `smt!`. Without this module `smt!` accepts none.
-/
-- Declared here rather than in `Cvc.Ext` so that the grammar a user gets is the grammar of the
-- theories they imported. The expander's own machinery lives in `Cvc.Ext`, never in `Cvc`.

public meta section

open Lean

/-- String literal. -/
syntax:max (name := smtStr) str : smtTerm

namespace Ext open Cvc.Ext

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.untyped do Macro.throwUnsupported
    unless t.raw.getKind == ``smtStr do Macro.throwUnsupported
    let s : TSyntax `term := ⟨t.raw[0]⟩
    `($(layer.op `mkStringValue) $s)

end Ext

end
