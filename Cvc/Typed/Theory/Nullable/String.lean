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

public import Cvc.Untyped.Theory.Nullable.String
public import Cvc.Typed.Theory.String
public import Cvc.Typed.Theory.Nullable.Defs
public import Cvc.Spec.String



/-! # Strings over nullables, typed

Each lifted operator has its plain counterpart's signature with an `Option` around every argument
and around the result, and nothing else changed. The lift is **strict**: `none` unless every
argument is `some`.

The indexed operators do not lift, for the reason bit-vectors' do not: an `Op` cannot be handed to
`mkNullableLift`.
-/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed_nullable% from Cvc.Spec.String
