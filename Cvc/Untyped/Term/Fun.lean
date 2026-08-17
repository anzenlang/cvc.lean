/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Term.Defs

public import Cvc.Untyped.Term.Defs
public import Cvc.Ext
public import Cvc.Gen
public import Cvc.Spec.Fun



/-! # Function-application constructors, sort-erased

`applyN` takes an array and `apply`/`apply2`/`apply3` are the fixed-arity spellings over it, so any
arity is reachable. All four build `APPLY_UF`, whose first child is the function itself.

**They flatten.** Applying a term that is *already* an `APPLY_UF` appends to its children rather
than nesting, so `apply2 (← apply f i) b` and `applyN f #[i, b]` build the same `(f i b)`. That
matters beyond tidiness: a nested application would have a partially applied — and therefore
function-sorted — term inside it, and cvc5 admits function-sorted terms only under a higher-order
logic. Flattening is what keeps ordinary uninterpreted functions out of `HO_`.

This is why these are hand-written rather than generated: a generated constructor applies its kind
blindly, and cannot look at the term it is applying.

**A partial application is legal.** cvc5 accepts fewer arguments than the function's arity and
gives the result the *remaining* function sort: applying `(-> Int Bool Int)` to one `Int` yields a
term of sort `(-> Bool Int)`. Too many arguments is an error, and so is none — `APPLY_UF` wants at
least two children, the function and one argument.

`applyHo` is the different one: it is `HO_APPLY`, consumes exactly one argument whatever the
arity, and needs a higher-order logic.
-/
namespace Cvc.Untyped.Term public section

variable [Ω]

gen_untyped% from Cvc.Spec.Fun

/-- Applies a function to the given arguments, however many.

Saturating when they fill the domain, and a *partial* application otherwise — cvc5 answers a term
of the remaining function sort rather than refusing. More arguments than the domain has is an
error, as is passing none.
-/
def applyN
  (f : Term) (args : Terms)
  (_h : 0 < args.size := by
    (try grind) <;> fail "failed to prove there is at least one argument")
: Env Term := runUnsafe fun tm => do
  if let some .APPLY_UF := f.getKind? then
    let kids : Terms := f.getChildren
    tm.mkTerm .APPLY_UF (kids ++ args)
  else tm.mkTerm .APPLY_UF (#[f] ++ args)

/-- Applies a function to one argument. -/
def apply (f arg : Term) : Env Term := applyN f #[arg]

/-- Applies a function to two arguments. -/
def apply2 (f fst snd : Term) : Env Term := applyN f #[fst, snd]

/-- Applies a function to three arguments. -/
def apply3 (f fst snd thd : Term) : Env Term := applyN f #[fst, snd, thd]
