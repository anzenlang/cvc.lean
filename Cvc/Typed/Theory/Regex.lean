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
