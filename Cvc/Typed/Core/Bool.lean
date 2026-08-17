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

public import Cvc.Untyped.Core.Bool
public import Cvc.Typed.Core.Defs
public import Cvc.Typed.Core.Value
public import Cvc.Gen
public import Cvc.Spec.Bool



/-! # Generated Boolean and sort-generic constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Bool

/-- A symbol of the sort `α` describes, naming `α` explicitly. -/
def mkSymbolAs (α : Type) [ToTyp α] (name : String) : Env (Term α) := mkSymbol name



/-! ## Values -/

@[inherit_doc T.isBoolValue]
def isBoolValue (term : Term Bool) : Bool := T.isBoolValue term
@[inherit_doc T.getBoolValue]
def getBoolValue (term : Term Bool) : Res Bool := T.getBoolValue term
@[inherit_doc T.getBoolValue?]
def getBoolValue? (term : Term Bool) : Option Bool := T.getBoolValue? term

instance : SrtLike Bool where
  valueToTerm := mkBool
  termToValue t := getBoolValue t
