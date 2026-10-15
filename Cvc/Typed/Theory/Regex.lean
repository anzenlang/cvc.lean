/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs

public import Cvc.Untyped.Theory.Regex
public import Cvc.Ext
public import Cvc.Typed.Core.Value
public import Cvc.Spec.Regex
public import Cvc.Typed.Theory.String
public meta import Cvc.Untyped.Theory.Regex
public meta import Cvc.Ext



/-! # Generated Regex constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Regex



/-! ## Values

A regular expression reads back only as a term for now: cvc5 exposes no accessor for the language
a constant regex denotes, and nothing reconstructs one from a `Cvc.Regex`.
-/

@[inherit_doc T.getRegexValue]
def getRegexValue (term : Term Regex) : Env Regex := T.getRegexValue term

instance : SrtLike Regex where
  valueToTerm _value := throwTodo "value-to-term for `Regex`"
  termToValue := getRegexValue

end

end Cvc.Typed.Term



/-! ## `regex!`

The syntax is declared beside the sort-erased constructors; this is the typed expansion, answering
an `Env (Term Regex)`. A regex term in scope, or a `![…]` escape, must be a `Term Regex`.
-/

namespace Cvc.Typed

/-- Typed `regex!`. -/
scoped syntax "regex! " smtRegex : term

macro_rules
  | `(regex! $r) => `(regexT! $r)

end Cvc.Typed

namespace Cvc

public meta section

@[inherit_doc regexT]
macro_rules
  | `(regexT! $r) => Ext.expandRegex Ext.Layer.typed r.raw

end

end Cvc
