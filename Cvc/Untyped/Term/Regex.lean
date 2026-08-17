/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Term.Defs

public import Cvc.Untyped.Term.Defs
public import Cvc.Ext
public import Cvc.Untyped.Term.Value
public import Cvc.Gen
public import Cvc.Spec.Regex



/-! # Generated Regex constructors, sort-erased -/
namespace Cvc.Untyped.Term public section

open cvc5 renaming Term → T

variable [Ω]

gen_untyped% from Cvc.Spec.Regex



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
