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
public import Cvc.Untyped.Core.Value
public import Cvc.Gen.Term
public import Cvc.Spec.Regex
-- a regex literal is a string literal lifted with `str.to_re`, so `regex!` needs strings
public import Cvc.Untyped.Theory.String
public meta import Cvc.Ext



/-! # Generated Regex constructors, sort-erased -/
namespace Cvc.Untyped.Term public section

open cvc5 renaming Term → T

variable [Ω]

gen_untyped% from Cvc.Spec.Regex
gen_untyped_view% from Cvc.Spec.Regex



/-! ## Values

A regular expression reads back only as a term for now: cvc5 exposes no accessor for the language
a constant regex denotes, and nothing reconstructs one from a `Cvc.Regex`.
-/

/-- The regular expression a term denotes. -/
def getRegexValue (term : Term) : Env Regex :=
  throwTodo s!"regex value extraction from a constant term: {term}"

instance : SrtLike Regex where
  valueToTerm _value := throwTodo "value-to-term for `Regex`"
  termToValue t := t.getRegexValue

end

end Cvc.Untyped.Term



/-! ## `regex!`

Regular expressions in the notation they are usually written in, building the same terms as the
`re…` constructors:

```lean
regex! ['a'-'z' '_'] ['a'-'z' '0'-'9' '_']*     -- an identifier
regex! digit+ ("." digit+)?                       -- `digit` a regex term in scope
regex! ("ab" | "cd"){2,3} ∖ "abab"
```

| form | meaning |
|---|---|
| `"abc"`, `'a'` | the literal string, the literal character |
| `x`, `![e]` | a regex term in scope, any Lean term of the layer's regex type |
| `.`, `∅` | any single character, the empty language (`.*` is every string) |
| `['a'-'z' '_']`, `[^ …]` | a character class: ranges and characters; its complement in `.` |
| `r*`, `r+`, `r?`, `r{n}`, `r{n,m}` | star, plus, option, exactly `n`, between `n` and `m` |
| `r s` | concatenation |
| `¬ r` | complement |
| `r ∩ s`, `r ∖ s` | intersection, difference |
| `r \| s` | union |

Postfix operators bind tightest, then complement, then concatenation, then `∩`/`∖`, then `|`, as
in the usual notation. A literal string is Lean's, so escapes are Lean's and a `"."` is a dot,
never "any character". No token is added that Lean does not already have.

`regex!` is `scoped` in each layer, as `smt!` is: `open Cvc.Untyped` selects this one, which
answers an `Env Term`; the typed one answers an `Env (Term Regex)`.
-/

namespace Cvc

/-- A regular expression, as `regex!` writes one. -/
declare_syntax_cat smtRegex (behavior := symbol)

/-- An item of a character class: a character, or a range of them. -/
declare_syntax_cat smtRegexClassItem (behavior := symbol)

/-- A single character. -/
syntax (name := smtRegexClassChar) char : smtRegexClassItem
/-- The characters from the first to the second, inclusive. -/
syntax (name := smtRegexClassRange) char "-" char : smtRegexClassItem

/-- A literal string. -/
syntax:max (name := smtRegexStr) str : smtRegex
/-- A literal character. -/
syntax:max (name := smtRegexChar) char : smtRegex
/-- A regex term in scope. -/
syntax:max (name := smtRegexIdent) ident : smtRegex
/-- Any Lean term of the layer's regex type. -/
syntax:max (name := smtRegexEscape) "![" term "]" : smtRegex
/-- Grouping. -/
syntax:max (name := smtRegexParen) "(" smtRegex ")" : smtRegex
/-- Any single character. -/
syntax:max (name := smtRegexAny) "." : smtRegex
/-- The empty language. -/
syntax:max (name := smtRegexNone) "∅" : smtRegex
/-- A character class. -/
syntax:max (name := smtRegexClass) "[" (ppSpace smtRegexClassItem)+ "]" : smtRegex
/-- A negated character class: any single character not in it. -/
syntax:max (name := smtRegexNotClass) "[" "^" (ppSpace smtRegexClassItem)+ "]" : smtRegex

/-- Zero or more. -/
syntax:max (name := smtRegexStar) smtRegex:max noWs "*" : smtRegex
/-- One or more. -/
syntax:max (name := smtRegexPlus) smtRegex:max noWs "+" : smtRegex
/-- Zero or one. -/
syntax:max (name := smtRegexOpt) smtRegex:max noWs "?" : smtRegex
/-- Exactly `n`. -/
syntax:max (name := smtRegexRepeat) smtRegex:max noWs "{" num "}" : smtRegex
/-- Between `n` and `m`, inclusive. -/
syntax:max (name := smtRegexLoop) smtRegex:max noWs "{" num "," num "}" : smtRegex

/-- Complement. -/
syntax:max (name := smtRegexComp) "¬" smtRegex:max : smtRegex

/-- Concatenation, by juxtaposition: flat, as application is in `smt!`. -/
syntax:lead (name := smtRegexSeq) smtRegex:max (ppSpace colGt smtRegex:max)+ : smtRegex

/-- Intersection. -/
syntax:20 (name := smtRegexInter) smtRegex:20 " ∩ " smtRegex:21 : smtRegex
/-- Difference. -/
syntax:20 (name := smtRegexDiff) smtRegex:20 " ∖ " smtRegex:21 : smtRegex
/-- Union. -/
syntax:10 (name := smtRegexUnion) smtRegex:10 " | " smtRegex:11 : smtRegex

/-- A sort-erased regex; `regex!` under `open Cvc.Untyped`. -/
syntax (name := regexU) "regexU! " smtRegex : term
/-- A typed regex; `regex!` under `open Cvc.Typed`. -/
syntax (name := regexT) "regexT! " smtRegex : term

namespace Untyped

/-- Sort-erased `regex!`. -/
scoped syntax "regex! " smtRegex : term

macro_rules
  | `(regex! $r) => `(regexU! $r)

end Untyped

public meta section

open Lean

namespace Ext

/-- Expands a `regex!` node into a term of the given layer, in `Env`. -/
partial def expandRegex (layer : Layer) (stx : Syntax) : MacroM (TSyntax `term) := do
  let op := layer.op
  -- a literal string, as a string term
  let str (s : String) : MacroM (TSyntax `term) :=
    `($(op `mkString) $(Syntax.mkStrLit s) false)
  -- the regex matching exactly a literal string
  let lit (s : String) : MacroM (TSyntax `term) := do `($(← str s) >>= $(op `strToRegex))
  -- a constructor applied to the expansions of some sub-expressions
  let app (fn : TSyntax `term) (kids : Array Syntax) : MacroM (TSyntax `term) := do
    let args ← kids.mapM (expandRegex layer)
    bindArgs args (binder := "smtRe") fun ids => `($fn $ids*)
  -- the union of a character class's items
  let classUnion (items : Array Syntax) : MacroM (TSyntax `term) := do
    let terms ← items.mapM fun item => do
      match item.getKind with
      | ``smtRegexClassChar => lit (String.singleton (item[0].isCharLit?.getD ' '))
      | _ =>
        let lo := String.singleton (item[0].isCharLit?.getD ' ')
        let hi := String.singleton (item[2].isCharLit?.getD ' ')
        bindArgs #[← str lo, ← str hi] (binder := "smtReRange") fun ids =>
          `($(op `reRange) $(ids[0]!) $(ids[1]!))
    let mut acc := terms[0]!
    for t in terms.extract 1 terms.size do
      acc ← bindArgs #[acc, t] (binder := "smtReClass") fun ids =>
        `($(op `reUnion) $(ids[0]!) $(ids[1]!))
    return acc
  -- the layer's regex term type, ascribed where the writer supplies a term so that a mismatch is
  -- reported there rather than against a binder of the expansion
  let reTy ← if layer == Layer.typed then `($(layer.name `Term) Cvc.Regex)
    else `($(layer.name `Term))
  match stx.getKind with
  | ``smtRegexStr => lit (stx[0].isStrLit?.getD "")
  | ``smtRegexChar => lit (String.singleton (stx[0].isCharLit?.getD ' '))
  | ``smtRegexIdent => withRef stx `(pure ($(⟨stx[0]⟩) : $reTy))
  | ``smtRegexEscape => withRef stx `(($(⟨stx[1]⟩) : $(mkIdent `Cvc.Env) $reTy))
  | ``smtRegexParen => expandRegex layer stx[1]
  | ``smtRegexAny => pure (op `reAllChar)
  | ``smtRegexNone => pure (op `reNone)
  | ``smtRegexClass => classUnion stx[1].getArgs
  | ``smtRegexNotClass =>
    let items ← classUnion stx[2].getArgs
    bindArgs #[op `reAllChar, items] (binder := "smtReNeg") fun ids =>
      `($(op `reDiff) $(ids[0]!) $(ids[1]!))
  | ``smtRegexStar => app (op `reStar) #[stx[0]]
  | ``smtRegexPlus => app (op `rePlus) #[stx[0]]
  | ``smtRegexOpt => app (op `reOpt) #[stx[0]]
  | ``smtRegexRepeat =>
    let n : TSyntax `term := ⟨stx[2]⟩
    app (← `($(op `reRepeat) $n)) #[stx[0]]
  | ``smtRegexLoop =>
    let lo : TSyntax `term := ⟨stx[2]⟩
    let hi : TSyntax `term := ⟨stx[4]⟩
    app (← `($(op `reLoop) $lo $hi)) #[stx[0]]
  | ``smtRegexComp => app (op `reComplement) #[stx[1]]
  | ``smtRegexSeq =>
    -- left to right, so `a b c` is `a ++ (b ++ c)` as the parser groups nothing
    let parts := #[stx[0]] ++ stx[1].getArgs
    let mut acc ← expandRegex layer parts.back!
    for part in parts.pop.reverse do
      let lhs ← expandRegex layer part
      acc ← bindArgs #[lhs, acc] (binder := "smtReSeq") fun ids =>
        `($(op `reConcat) $(ids[0]!) $(ids[1]!))
    return acc
  | ``smtRegexInter => app (op `reInter) #[stx[0], stx[2]]
  | ``smtRegexDiff => app (op `reDiff) #[stx[0], stx[2]]
  | ``smtRegexUnion => app (op `reUnion) #[stx[0], stx[2]]
  | kind => Macro.throwErrorAt stx s!"unsupported regex (kind `{kind}`)"

end Ext

@[inherit_doc regexU]
macro_rules
  | `(regexU! $r) => Ext.expandRegex Ext.Layer.untyped r.raw

end

end Cvc
