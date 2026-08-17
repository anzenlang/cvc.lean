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

public import Cvc.Untyped.Theory.Nullable.Bool
public import Cvc.Typed.Theory.Nullable.Defs
public import Cvc.Gen
public import Cvc.Spec.Bool



/-! # Boolean and sort-generic over nullables, typed

Each lifted operator has its plain counterpart's signature with an `Option` around every argument
and around the result, and nothing else changed. The lift is **strict**: `none` unless every
argument is `some`.

**`equal?` is not `Option`'s equality.** The lift is strict, so `equal?` of two `none`s is `none`,
not `some true`. The same goes for `distinct?` and for `ite?`, which is strict in its condition.
-/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed_nullable% from Cvc.Spec.Bool
