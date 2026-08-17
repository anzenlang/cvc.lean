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

public import Cvc.Untyped.Theory.Seq
public import Cvc.Typed.Core.Value
public import Cvc.Gen
public import Cvc.Spec.Seq



/-! # Generated Seq constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Seq



/-! ## Values -/

@[inherit_doc T.isSeqValue]
def isSeqValue (term : Term (Array α)) : Bool := T.isSeqValue term


/-- The elements a constant sequence term denotes. -/
def getSeqValue [TermToValue α] (term : Term (Array α)) : Env (Array α) :=
  have := TermToValue.toUntyped (α := α)
  T.getSeqValue term

@[inherit_doc getSeqValue]
def getSeqValueOf (α : Type) [TermToValue α] : (term : Term (Array α)) → Env (Array α) :=
  getSeqValue

/-- The sequence term denoting an array of values. -/
def mkSeqValue [ToTyp α] [ValueToTerm α] : (elems : Array α) → Env (Term (Array α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkSeqValue

instance [ToTyp α] [ValueToTerm α] : ValueToTerm (Array α) := ⟨mkSeqValue⟩
instance [TermToValue α] : TermToValue (Array α) := ⟨getSeqValue⟩
