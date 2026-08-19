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
public import Cvc.Untyped.Theory.Float
public import Cvc.Untyped.Theory.Nullable.Defs
public import Cvc.Spec.Float



/-! # Floating point over nullables, sort-erased

One lifted constructor per liftable operator, `<id>?`, each answering `none` unless every argument
is `some`. That strictness is `nullable.lift`'s semantics and not a choice made here.

A rounding-mode argument becomes nullable along with the rest: `fpAdd?` takes a
`Term (Option Float.RoundingMode)`, since `nullable.lift` makes every argument of the lifted
operator nullable and none of them optional.
-/
namespace Cvc.Untyped.Term public section variable [Ω]

gen_untyped_nullable% from Cvc.Spec.Float
