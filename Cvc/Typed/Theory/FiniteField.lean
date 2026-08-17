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

public import Cvc.Types.FiniteField
public import Cvc.Untyped.Theory.FiniteField
public import Cvc.Ext
public import Cvc.Typed.Core.Value
public import Cvc.Gen
public import Cvc.Spec.FiniteField



/-! # Generated FiniteField constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.FiniteField



/-! ## Values -/

@[inherit_doc T.isFiniteFieldValue]
def isFiniteFieldValue (term : Term (Cvc.FiniteField size)) : Bool :=
  T.isFiniteFieldValue term

@[inherit_doc T.getFiniteFieldRepr]
def getFiniteFieldRepr (term : Term (Cvc.FiniteField size)) : Res Int :=
  T.getFiniteFieldRepr term


/-- The term denoting an element of a finite field. -/
def mkFiniteFieldValue
: (elem : Cvc.FiniteField size) → Env (Term (Cvc.FiniteField size)) :=
  T.FiniteField.toTerm

/-- The finite-field element a constant term denotes. -/
def getFiniteFieldValue
: Term (Cvc.FiniteField size) → Env (Cvc.FiniteField size) := T.FiniteField.ofTerm

instance : SrtLike (Cvc.FiniteField size) where
  valueToTerm := mkFiniteFieldValue
  termToValue := getFiniteFieldValue
