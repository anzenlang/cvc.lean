/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs

public import Cvc.Srt
public import Cvc.Types.Tuple
public import Cvc.Untyped.Theory.Tuple
public import Cvc.Typed.Core.Value



/-! # Tuples, typed

A tuple's index is a Lean product, and products **flatten to the right** exactly as function sorts
curry: `α × β × γ` denotes `(Tuple α β γ)`, one tuple of three components, not a pair whose second
component is a pair. Left-nesting is what nests, so `(α × β) × γ` is the two-component tuple whose
first component is a tuple.

That is what shapes the constructor below. A tuple's components are held flat, because the sort is
flat, and `Components` is the only way to collect them — its two builders keep the array and the
index in step. A tuple's *last* component is the one case the index cannot describe: a product
there would flatten into the tuple being built while the component term would not, so `last` asks
for a proof that its index is not a product. Anywhere else a product component is fine, since it
nests.
-/
namespace Cvc.Typed.Term public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## Construction -/

/-- The components of a tuple, flat, along with the index they denote.

`last` and `cons` are the only ways to build one, and between them they keep the number of terms
equal to the number of components the index describes.
-/
structure Components (α : Type) where
  private mk ::
  private terms : Untyped.Terms

namespace Components

/-- The last component of a tuple.

Its index must not itself be a product: `α × β` flattens `β`'s components into the tuple being
built, and a single term cannot stand for several of them. Nest to the *left* instead — a
`Term ((γ × δ) × ε)` really is a tuple whose first component is a tuple.
-/
def last [ToTyp α] (component : Term α)
  (_isFlat : (Typ.of α).isFlat := by
    (try simp [Typ.isFlat, Typ.of, ToTyp.typ, Srt.prod]) <;>
      fail "a tuple's last component cannot itself be a tuple: its components would flatten into \
        the tuple being built. Nest to the left instead.")
: Components α := ⟨#[component.erase]⟩

/-- Adds a component in front of the ones collected so far. -/
def cons [ToTyp α] (component : Term α) (rest : Components β) : Components (α × β) :=
  ⟨#[component.erase] ++ rest.terms⟩

end Components

/-- The tuple whose components are the given ones, in order.

A tuple has at least two components, which is why the first is separate: `Components` on its own
describes a single index, and only `α × β` describes a tuple.
-/
def mkTuple [ToTyp α] (fst : Term α) (rest : Components β) : Env (Term (α × β)) :=
  T.mkTuple (#[fst.erase] ++ rest.terms)

/-- The tuple of the components at the given indices, in the order given.

The result is sort-erased: which components an index array selects is a runtime value, so no Lean
index describes it. `Untyped.Term.typeCheck` puts an index back on once you know what it is.
-/
def tupleProject [ToTyp α] (indices : Array Nat) (tuple : Term α) : Env Untyped.Term :=
  T.tupleProject indices tuple



/-! ## Values -/

@[inherit_doc T.isTupleValue]
def isTupleValue [ToTyp α] [ToTyp β] (term : Term (α × β)) : Bool := T.isTupleValue term

/-- The components a constant tuple term denotes, failing if it denotes none.

Sort-erased, like `getKids`: a tuple's components have as many different indices as it has
components, and an array holds one type.
-/
def getTupleValue [ToTyp α] [ToTyp β] (term : Term (α × β)) : Res Untyped.Terms :=
  T.getTupleValue term



/-! ## Selection

`fst` and `snd` read a tuple the way Lean's `Prod.fst` and `Prod.snd` read a product, which is what
makes them work at every arity rather than only on pairs.

Right-flattening is the reason that matters. `Term (α × β)` describes a two-component tuple when
`β` is flat, but a longer one when `β` is itself a product — and `β` then stands for *all* the
remaining components. So `snd` cannot be component 1: on `α × β × γ` it has to answer the tuple
`(Tuple β γ)`, exactly as Lean's `snd` on `α × (β × γ)` answers the pair. That is what it does, and
it is why the index it claims always matches the sort it builds.

Reading a *single* component out of the middle of a longer tuple is a different operation, and has
no typed form yet: `Untyped.Term.tupleSelect` followed by `typeCheck` is the way to one.
-/

/-- The first component, as Lean's `Prod.fst`.

Sound at any arity: whatever else a tuple holds, its first component is what the index's first
factor describes.
-/
def fst (t : Term (α × β)) : Env (Term α) := do
  t.erase.tupleSelect 0

/-- Everything but the first component, as Lean's `Prod.snd`.

On a two-component tuple that is the second component. On a longer one `β` describes the whole
tail, so this answers the tuple of every component past the first — `(Tuple β γ)` for an
`α × β × γ`, never just `β`.

The tail is rebuilt from its components rather than projected, so the term reads
`(tuple (tuple.select 1 t) (tuple.select 2 t))`. That is equal to `tupleProject #[1, 2] t`; the
solver proves it.
-/
def snd [B : ToTyp β] (t : Term (α × β)) : Env (Term β) := do
  let t := t.erase
  match B.typ with
  -- `β` is itself a product, so the tuple runs past two components and the tail is a tuple
  | .prod tys =>
    let mut terms := Array.mkEmpty tys.length
    for i in 1 ...= tys.length do
      let sub ← t.tupleSelect i
      terms := terms.push sub
    Untyped.Term.mkTuple terms
  -- `β` is flat, so the tuple has exactly two components and the tail is the second
  | _ => t.tupleSelect 1
