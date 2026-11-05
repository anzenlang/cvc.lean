/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Function-application specification

Function sorts are curried, so `fn α (fn β γ)` is the SMT sort `(-> α β γ)`. Two ways to
apply one:

Only `applyHo` is specified here. It consumes a single argument and returns whatever the codomain
is, so it can partially apply a multi-argument function — and needs a higher-order logic for it.

`APPLY_UF` application is hand-written in `{Untyped,Typed}/Term/Fun.lean` instead, because the
constructors have to *flatten*: applying an `APPLY_UF` term to more arguments appends to its
children rather than nesting, which is what keeps a term free of the function-sorted intermediates
a higher-order logic would otherwise be needed for. A generated constructor cannot look at the term
it is applying.
-/
namespace Cvc public section

/-- Application of a single argument, leaving any remaining ones unapplied. -/
op% applyHo {α β} (f : fn α β) (arg : α) : β := HO_APPLY
