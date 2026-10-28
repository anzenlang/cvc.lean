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

public import Cvc.Untyped.Theory.Fun
public import Cvc.Gen.TypedView
public import Cvc.Typed.Core.View
public import Cvc.Typed.Core.Defs
public import Cvc.Ext
public import Cvc.Spec.Fun



/-! # Function-application constructors, typed

A function's index is the curried arrow `α → β → γ`, which `Typ.toSrt` flattens into the SMT sort
`(-> α β γ)`. `applyN` takes an `Args` spine and so covers every arity; `apply`/`apply2`/`apply3`
are the fixed-arity spellings over it.

**They flatten**, inheriting that from the sort-erased constructors: applying a term that is
already an `APPLY_UF` appends to its children rather than nesting. So the `CoeFun` chain `f a b c`
builds the same flat term `applyN` does, and stays clear of the function-sorted intermediates that
would otherwise force a higher-order logic.

**`Args φ β` is the arguments that take a `φ` down to a `β`**, and the spine you build is what says
how many there are. `done` is an explicit base case, so nothing ever has to ask whether `β` is
"still an arrow" — the question that makes drop-last on a right-nested index intractable.

Stopping the spine early is a **partial application**, and it is sound: cvc5 accepts fewer
arguments than the arity and gives the term the remaining function sort, which is exactly the `β`
the spine computes.
-/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Fun
gen_typed_view% from Cvc.Spec.Fun



/-! ## Applying any number of arguments -/

/-- Arguments taking a function of index `φ` down to a result of index `β`.

`last` and `cons` are the only builders, so the terms collected and the arrows consumed stay in
step — and `last` carrying an argument is what makes "at least one" structural, where an array
would have needed a side condition.
-/
structure Args (φ : Type) (β : Type) where private mk ::
  private terms : Untyped.Terms
  -- carried, not re-proved at the use site: `applyN` needs it and only the builders know it
  private nonEmpty : 0 < terms.size

namespace Args

/-- The final argument. Its `β` is whatever the function has left, so stopping here is a partial
application. -/
def last (arg : Term α) : Args (α → β) β where
  terms := #[arg.erase]
  nonEmpty := by simp

/-- One more argument, in front of the ones collected so far. -/
def cons (arg : Term α) (rest : Args φ β) : Args (α → φ) β where
  terms := #[arg.erase] ++ rest.terms
  nonEmpty := by grind only [
    usr Array.eq_empty_of_size_eq_zero, = Array.size_append,
    = List.size_toArray, = List.length_cons
  ]

end Args

/-- Applies a function to the arguments a spine holds.

Saturating when they fill the domain, and a partial application otherwise — the spine's `β` is the
remaining function index in that case, and cvc5 gives the term that very sort.

There is always at least one argument, since `Args.last` carries one. That is what `APPLY_UF`
requires, and it costs no side condition here.
-/
def applyN (f : Term φ) (args : Args φ β) : Env (Term β) :=
  T.applyN f.erase args.terms args.nonEmpty

instance : CoeFun (Term (α → β)) (fun _ => Term α → Env (Term β)) where
  coe f arg := f.applyN (.last arg)

instance : CoeFun (Env (Term (α → β))) (fun _ => Term α → Env (Term β)) where
  coe f arg := do (← f) arg

/-- Applies a function to one argument. -/
def apply (f : Term (α → β)) (arg : Term α) : Env (Term β) := applyN f (.last arg)

/-- Applies a function to two arguments. -/
def apply2 (f : Term (α → β → γ)) (fst : Term α) (snd : Term β) : Env (Term γ) :=
  applyN f (.cons fst (.last snd))

/-- Applies a function to three arguments. -/
def apply3 (f : Term (α → β → γ → δ)) (fst : Term α) (snd : Term β) (thd : Term γ)
: Env (Term δ) :=
  applyN f (.cons fst (.cons snd (.last thd)))

end

end Cvc.Typed.Term



/-! ## Viewing an application

Hand-written, since application flattens and its arity is arbitrary: `Cvc.Spec.Fun` only specifies
`applyHo`, whose view `View.Fun` is generated. The arguments' sorts are whatever the function's
domain is, which the application's sort does not fix, so they are a list of `Typ`s from which the
function's index is computed. Matching on the list refines both: `.apply [.int, .bool] f (.cons x
(.last b))` gives `f : Term (Int → Bool → τ.Denote)`, `x : Term Int` and `b : Term Bool`.
-/

namespace Cvc.Typed public section variable [Ω]

/-- An application's arguments, each at the denotation of its sort; never empty. -/
inductive View.Apply.Args : List Typ → Type where
  /-- The last argument. -/
  | last (t : Term τ.Denote) : View.Apply.Args [τ]
  /-- One more argument, in front of the others. -/
  | cons (t : Term τ.Denote) (rest : View.Apply.Args τs) : View.Apply.Args (τ :: τs)

/-- The same arguments as an application spine, so that a viewed application can be rebuilt. -/
def View.Apply.Args.toArgs : View.Apply.Args doms → Term.Args (Typ.arrows doms β) β
  | .last t => .last t
  | .cons t rest => .cons t rest.toArgs

/-- An uninterpreted function's application, of sort `τ`, taken apart one level. -/
protected inductive View.Apply : Typ → Type where
  /-- `f a₁ … aₙ`, fully applied. -/
  | apply {τ : Typ} (doms : List Typ) (f : Term (Typ.arrows doms τ.Denote))
    (args : View.Apply.Args doms) : View.Apply τ

/-- Takes a term of sort `τ` apart one level, if it is an uninterpreted function's application whose
arguments' sorts a `Typ` describes. -/
def View.Apply.of (τ : Typ) (t : Term τ.Denote) : Env (Option (View.Apply τ)) := do
  let some (.apply f args) := Untyped.View.Apply.of? t.erase | return none
  let some ⟨doms, args⟩ ← go args.val.toList | return none
  return some (.apply doms (View.reindex f) args)
where
  /-- The arguments, with their sorts. -/
  go : List Untyped.Term → Env (Option ((doms : List Typ) × View.Apply.Args doms))
    | [] => return none
    | [k] => do
      let some σ ← View.typOf? k | return none
      return some ⟨[σ], .last (View.reindex k)⟩
    | k :: ks => do
      let some σ ← View.typOf? k | return none
      let some ⟨σs, rest⟩ ← go ks | return none
      return some ⟨σ :: σs, .cons (View.reindex k) rest⟩

register_typed_view% Cvc.Typed.View.Apply [apply APPLY_UF]

end

end Cvc.Typed
