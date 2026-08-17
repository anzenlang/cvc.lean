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

public import Cvc.Types.Set
public import Cvc.Untyped.Theory.Set
public import Cvc.Typed.Core.Value
public import Cvc.Gen
public import Cvc.Spec.Set



/-! # Generated Set constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Set



/-! ## Values -/

@[inherit_doc T.isSetValue]
def isSetValue [Ord α] (term : Term (Cvc.Set α)) : Bool := T.isSetValue term


section variable [Ord α] [ToTyp α]

/-- The set term denoting a set of values. -/
def mkSetValue [ValueToTerm α] : (set : Cvc.Set α) → Env (Term (Cvc.Set α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkSetValue

/-- The set of values a constant set term denotes. -/
def getSetValue [TermToValue α] : Term (Cvc.Set α) → Env (Cvc.Set α) :=
  have := TermToValue.toUntyped (α := α)
  T.getSetValue

instance [ValueToTerm α] : ValueToTerm (Cvc.Set α) := ⟨mkSetValue⟩
instance [TermToValue α] : TermToValue (Cvc.Set α) := ⟨getSetValue⟩

end
