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



/-! # Function application, typed

A function's index is the curried arrow `α → β → γ`, the SMT sort `(-> α β γ)`. A function term
applies directly, `f a b : Env (Term γ)`, or through `apply`/`apply2`/`apply3`, or
`applyN f (.cons a (.last b))` at any arity. Fewer arguments than the arity is a partial
application, at the remaining function index.

Applications flatten: applying a term that is already an application appends to its arguments, so
all these spellings build the same flat term, which needs no higher-order logic.
-/
-- `Args` has an explicit base case, `last`, so nothing ever has to ask whether `β` is "still an
-- arrow" — the question that makes drop-last on a right-nested index intractable.
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.Fun
gen_typed_view% from Cvc.Spec.Fun



/-! ## Applying any number of arguments -/

/-- Arguments taking a function of index `φ` down to a result of index `β`, at least one.

Built with `last` and `cons`: `.cons a (.last b)` is `a` then `b`.
-/
structure Args (φ : Type) (β : Type) where private mk ::
  private terms : Untyped.Terms
  -- carried, not re-proved at the use site: `applyN` needs it and only the builders know it
  private nonEmpty : 0 < terms.size

namespace Args

/-- The final argument; `β` is whatever the function has left, a function sort if it is partial. -/
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

/-- The arguments' terms, sort-erased and in order, as the sort-erased `Term.applyN` takes them. -/
def toUntyped (args : Args φ β) : Untyped.Terms := args.terms

@[inherit_doc toUntyped]
abbrev erase (args : Args φ β) : Untyped.Terms := args.toUntyped

end Args

/-- Applies a function to some arguments: all of them, or fewer for a partial application. -/
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

The arguments' sorts come as a list of `Typ`s, from which the function's index is computed, and
matching on the list refines both: `.apply [.int, .bool] f (.cons x (.last b))` gives
`f : Term (Int → Bool → τ.Denote)`, `x : Term Int` and `b : Term Bool`.
-/
-- Hand-written, since application flattens and its arity is arbitrary: `Cvc.Spec.Fun` only
-- specifies `applyHo`, whose view `View.Fun` is generated.

namespace Cvc.Typed public section variable [Ω]

/-- An application's arguments, each a `Term σ.Denote` at its sort `σ`; never empty. -/
inductive View.Apply.Args : List Typ → Type where
  /-- The last argument. -/
  | last (t : Term τ.Denote) : View.Apply.Args [τ]
  /-- One more argument, in front of the others. -/
  | cons (t : Term τ.Denote) (rest : View.Apply.Args τs) : View.Apply.Args (τ :: τs)

/-- The same arguments as a `Term.Args`, so that a viewed application can be rebuilt. -/
def View.Apply.Args.toArgs : View.Apply.Args doms → Term.Args (Typ.arrows doms β) β
  | .last t => .last t
  | .cons t rest => .cons t rest.toArgs

/-- An uninterpreted function's application, of sort `τ`, taken apart one level. -/
protected inductive View.Apply : Typ → Type where
  /-- `f a₁ … aₙ`, fully applied. -/
  | apply {τ : Typ} (doms : List Typ) (f : Term (Typ.arrows doms τ.Denote))
    (args : View.Apply.Args doms) : View.Apply τ

/-- Takes a function application of sort `τ` apart one level, `none` for any other term.

Also `none` when an argument's sort is one no `Typ` describes.
-/
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
