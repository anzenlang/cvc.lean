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

public import Cvc.Types.Bag
public import Cvc.Untyped.Theory.Bag
public import Cvc.Typed.Core.Value
public import Cvc.Gen
public import Cvc.Spec.Bag



/-! # Generated Bag constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Bag



/-! ## Values -/

section variable [Ord α] [ToTyp α]

/-- The bag term denoting a bag of values. -/
def mkBagValue [ValueToTerm α] : (bag : Cvc.Bag α) → Env (Term (Cvc.Bag α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkBagValue

/-- The bag of values a constant bag term denotes. -/
def getBagValue [TermToValue α] : Term (Cvc.Bag α) → Env (Cvc.Bag α) :=
  have := TermToValue.toUntyped (α := α)
  T.getBagValue

instance [ValueToTerm α] : ValueToTerm (Cvc.Bag α) := ⟨mkBagValue⟩
instance [TermToValue α] : TermToValue (Cvc.Bag α) := ⟨getBagValue⟩

end
