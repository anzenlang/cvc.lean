/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

-- the plain theory, for the constructors backing the `N'` variants' unit elements; `nullableSome`
-- wraps one, since a lifted operator's unit is nullable too
public import Cvc.Untyped.Theory.FiniteField
public import Cvc.Untyped.Theory.Nullable.Defs
public import Cvc.Gen
public import Cvc.Spec.FiniteField



/-! # Finite fields over nullables, sort-erased

One lifted constructor per liftable operator, `<id>?`, each answering `none` unless every argument
is `some`. That strictness is `nullable.lift`'s semantics and not a choice made here.

The field's size is an index on the sort, not an operator index, so every operator here lifts.
-/
namespace Cvc.Untyped.Term public section variable [Ω]

gen_untyped_nullable% from Cvc.Spec.FiniteField
