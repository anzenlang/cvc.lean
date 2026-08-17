/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Term.Defs
import all Cvc.Typed.Term.Defs

public import Cvc.Types.Array
public import Cvc.Untyped.Term.Array
public import Cvc.Typed.Term.Defs
public import Cvc.Typed.Term.Value
public import Cvc.Gen
public import Cvc.Spec.Array



/-! # Generated Array constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Array



/-! ## Values -/

@[inherit_doc T.isConstArray]
def isConstArray [Ord α] (term : Term (Cvc.TotalMap α β)) : Bool := T.isConstArray term


section variable [Ord α] [ToTyp α] [ToTyp β]

/-- The array term denoting a total map. -/
def mkArrayValue [ValueToTerm α] [ValueToTerm β]
: Cvc.TotalMap α β → Env (Term (Cvc.TotalMap α β)) :=
  have := ValueToTerm.toUntyped (α := α)
  have := ValueToTerm.toUntyped (α := β)
  T.mkArrayValue

/-- The total map a constant array term denotes. -/
def getArrayValue [TermToValue α] [TermToValue β]
: Term (Cvc.TotalMap α β) → Env (Cvc.TotalMap α β) :=
  have := TermToValue.toUntyped (α := α)
  have := TermToValue.toUntyped (α := β)
  T.getArrayValue

instance [ValueToTerm α] [ValueToTerm β] : ValueToTerm (Cvc.TotalMap α β) := ⟨mkArrayValue⟩
instance [TermToValue α] [TermToValue β] : TermToValue (Cvc.TotalMap α β) := ⟨getArrayValue⟩

end
