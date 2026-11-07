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

So a tuple's *last* component cannot itself be a tuple: `mkTuple x (.cons y (.last z))` builds
a `Term (α × β × γ)`, and `Components.last` refuses a product. Relations and tables use another
tuple index, `Tup α β` in `Cvc.Typed.Theory.Relation`, which nests freely and reaches any component
at a typed position.
-/
namespace Cvc.Typed.Term public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## Construction -/

/-- Components of a tuple, built with `last` and `cons`: `.cons y (.last z)` is `y` then `z`. -/
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

/-- The components' terms, sort-erased and flat, as the sort-erased `Term.mkTuple` takes them. -/
def toUntyped (cs : Components α) : Untyped.Terms := cs.terms

@[inherit_doc toUntyped]
abbrev erase (cs : Components α) : Untyped.Terms := cs.toUntyped

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

`fst` and `snd` read a tuple as Lean's `Prod.fst` and `Prod.snd` read a product: on an
`α × β × γ`, `snd` answers the tuple `(Tuple β γ)`. A single middle component has no typed accessor
here: use `Untyped.Term.tupleSelect` then `typeCheck`, or the `Tup` index, whose `tupAt` reaches
any component.
-/

/-- The first component, as Lean's `Prod.fst`, at any arity. -/
def fst (t : Term (α × β)) : Env (Term α) := do
  t.erase.tupleSelect 0

/-- Everything but the first component, as Lean's `Prod.snd`.

The second component of a pair; on a longer tuple, the tuple of every component past the first —
`(Tuple β γ)` for an `α × β × γ`, built as `(tuple (tuple.select 1 t) (tuple.select 2 t))`.
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

/-- A pair literal's two components, `none` if the term is not a literal.

Pairs only: a longer tuple's tail has no term of its own. The datatype view takes any tuple apart.
-/
def pairComponents? [ToTyp β] (t : Term (α × β))
  (_isFlat : (Typ.of β).isFlat := by
    (try simp [Typ.isFlat, Typ.of, ToTyp.typ, Srt.prod]) <;>
      fail "the second component is a tuple, so this is not a pair")
: Env (Option (Term α × Term β)) := do
  let raw := t.erase
  unless raw.getKind? == some .APPLY_CONSTRUCTOR do return none
  -- the first kid is the constructor
  match raw.getKids.toList with
  | [_, a, b] => return some ((a : Term α), (b : Term β))
  | _ => throwInternal s!"`{raw}`: not a pair"
