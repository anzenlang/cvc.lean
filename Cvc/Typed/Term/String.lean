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

public import Cvc.Untyped.Term.String
public import Cvc.Typed.Term.Defs
public import Cvc.Typed.Term.Value
public import Cvc.Gen
public import Cvc.Spec.String



/-! # Generated String constructors, typed -/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.String



/-! ## Values -/

@[inherit_doc T.isStringValue]
def isStringValue (term : Term String) : Bool := T.isStringValue term
@[inherit_doc T.getStringValue]
def getStringValue (term : Term String) : Res String := T.getStringValue term
@[inherit_doc T.getStringValue?]
def getStringValue? (term : Term String) : Option String := T.getStringValue? term

instance : SrtLike String where
  valueToTerm s := mkString s false
  termToValue t := getStringValue t
