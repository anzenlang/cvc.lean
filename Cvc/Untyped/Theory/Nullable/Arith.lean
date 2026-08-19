/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

-- the plain theory, for the constructor backing the `N'` variants' unit element (`mkInt` here);
-- `nullableSome` wraps it, since a lifted operator's unit is nullable too
public import Cvc.Untyped.Theory.Arith
public import Cvc.Untyped.Theory.Nullable.Defs
public import Cvc.Gen
public import Cvc.Spec.Arith



/-! # Arithmetic over nullables, sort-erased

One lifted constructor per liftable arithmetic operator, `<id>?`. Each answers `none` unless every
argument is `some`, which is `nullable.lift`'s semantics and not a choice made here.

This module is separate from `Untyped/Term/Arith.lean` so that a user who wants `Option Int` pays
for arithmetic alone, and one who does not pays nothing.
-/
namespace Cvc.Untyped.Term public section variable [Ω]

gen_untyped_nullable% from Cvc.Spec.Arith
