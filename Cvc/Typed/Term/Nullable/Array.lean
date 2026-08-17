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

public import Cvc.Untyped.Term.Nullable.Array
public import Cvc.Typed.Term.Array
public import Cvc.Typed.Term.Defs
public import Cvc.Typed.Term.Nullable
public import Cvc.Gen
public import Cvc.Spec.Array



/-! # Arrays over nullables, typed

Each lifted operator has its plain counterpart's signature with an `Option` around every argument
and around the result, and nothing else changed. The lift is **strict**: `none` unless every
argument is `some`.

`select?` and `store?` take and answer nullable terms: it is the array *term* that becomes
nullable, not its indices or elements. An array whose elements are themselves nullable is a
different thing, written `TotalMap α (Option β)`.
-/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed_nullable% from Cvc.Spec.Array
