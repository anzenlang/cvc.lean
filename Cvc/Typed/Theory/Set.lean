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
public import Cvc.Gen.TypedView
public import Cvc.Typed.Core.View
public import Cvc.Untyped.Theory.Set
public import Cvc.Typed.Core.Value
public import Cvc.Spec.Set
public import Cvc.Typed.Core.BVar

import all Cvc.Typed.Core.BVar



/-! # Generated Set constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Set
gen_typed_view% from Cvc.Spec.Set



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



/-! ## Comprehension

`{ elem | bvs. pred }`, whose index is the element's: the bound variables' sorts do not reach the
result. See `Cvc.Untyped.Term.setComprehension` for what cvc5 supports of it.
-/

/-- The set of the values `elem` takes, over the bindings of `bvs` that satisfy `pred`. -/
def setComprehension [ToTyp β] [Ord β] (bvs : BVars) (pred : Term Bool) (elem : Term β)
  (_nonEmpty : bvs ≠ [] := by
    (try simp) <;> fail "failed to prove a comprehension binds at least one variable")
: Env (Term (Cvc.Set β)) :=
  T.setComprehension bvs.relax pred elem (by cases bvs <;> simp_all [BVars.relax])
