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

public import Cvc.Untyped.Term.Nullable.FiniteField
public import Cvc.Typed.Term.FiniteField
public import Cvc.Typed.Term.Defs
public import Cvc.Typed.Term.Nullable
public import Cvc.Gen
public import Cvc.Spec.FiniteField



/-! # Finite fields over nullables, typed

Each lifted operator has its plain counterpart's signature with an `Option` around every argument
and around the result, and nothing else changed. The lift is **strict**: `none` unless every
argument is `some`.

The field's size is an index on the sort, not an operator index, so every operator here lifts.
-/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed_nullable% from Cvc.Spec.FiniteField
