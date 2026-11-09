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
public import Cvc.Gen.TypedView
public import Cvc.Typed.Core.View
public import Cvc.Ext
public import Cvc.Typed.Core.Value
public import Cvc.Spec.Regex
public import Cvc.Typed.Theory.String
public meta import Cvc.Untyped.Theory.Regex
public meta import Cvc.Ext



/-! # Regular expressions, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Regex
gen_typed_view% from Cvc.Spec.Regex



/-! ## Values

A regular expression has no Lean value: cvc5 exposes no accessor for the language a constant regex
denotes, so `Regex` has no value conversions. Read a model's regex as a term, with
`Solver.getValueTerm`.
-/

end

end Cvc.Typed.Term



/-! ## `regex!`

`regex! "ab" ['0'-'9']+ | .*` writes a regular expression in the usual notation, as an
`Env (Term Regex)`. A regex term in scope, or a `![…]` escape, must be a `Term Regex`.
-/
-- The syntax is declared beside the sort-erased constructors; this is the typed expansion.

namespace Cvc.Typed

/-- A regular expression in the usual notation, as an `Env (Term Regex)`: `regex! "a"+ | .*`. -/
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
