/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt

public meta import Lean.Elab.Command



/-! # Indices for tuples, relations and tables

A tuple's components are a **list**, and this is the index that says so: `Tup α β` describes the
components `α ++ [β]`. Splitting the last one off does two jobs at once.

It makes the list *non-empty*, since a tuple has at least one component. And — the part that earns
the encoding — it makes "the last component" a **parameter position**, so unification can find it.
`?α ++ [?β]` against a concrete list is higher-order and Lean will not solve it; `Tup ?α ?β` against
`Tup [Int, Bool] Real` is first-order and solves at once. That is what lets relational join say
"drop the left's last and the right's first" as nothing but a signature:

```lean
relJoin : Term (Rel α μ) → Term (Rel (μ :: α') β') → Env (Term (Rel (α ++ α') β'))
```

with the shared `μ` expressing, structurally, cvc5's requirement that the two be joinable.

**This is why `α × β` was not enough.** A right-nested product has no terminator, so the slot for
"rest of the tuple" and the slot for "last component" are the same one: `α × (β × γ)` cannot say
whether it means three components or two whose second is a pair. `Tup [α] (β × γ)` and
`Tup [α, β] γ` are different indices, and denote different sorts.

`Rel` and `Tab` are sets and bags of tuples. Neither is a sort of its own — cvc5 has no
`RELATION_SORT` or `TABLE_SORT` — so these are indices over the same underlying terms, and
`toSet`/`toBag` cross over for free.
-/
namespace Cvc public section



/-- The `Typ`s a list of Lean types denotes. -/
class ToTypList (α : List Type) where
  /-- The `Typ`s, in order. -/
  typs : List Typ

namespace ToTypList

instance : ToTypList [] := ⟨[]⟩

instance [A : ToTyp α] [As : ToTypList αs] : ToTypList (α :: αs) := ⟨A.typ :: As.typs⟩

/-- The `Typ`s of `α ++ [β]`, which is what every index here describes. -/
def typsOf (α : List Type) (β : Type) [As : ToTypList α] [B : ToTyp β] : List Typ :=
  As.typs ++ [B.typ]

end ToTypList



/-- A tuple of the components `α ++ [β]`.

Carries no data: it names a sort, and the terms it indexes are ordinary terms. Built with
`Term.mkTuple` from a `Components` spine.
-/
structure Tup (α : List Type) (β : Type) where
  private mk ::

/-- A relation over the components `α ++ [β]`: a **set** of `Tup α β`. -/
structure Rel (α : List Type) (β : Type) where
  private mk ::

/-- A table over the columns `α ++ [β]`: a **bag** of `Tup α β`, so a row may repeat. -/
structure Tab (α : List Type) (β : Type) where
  private mk ::

/-! ### Instances for nesting

These indices carry no data — they name a sort — so their comparisons are trivial. They exist only
so that a container of them can be *spelled*: `relGroup` answers a `Set (Rel α β)`, and `Set` wants
its element ordered. No `Std.TreeSet` of relations is ever built, since these indices have no value
conversion, so the triviality never shows.

They are written out rather than derived because `deriving` constrains the type parameters even
though nothing uses them, which would demand `Ord β` — and `Ord Rat` does not exist.
-/

instance : DecidableEq (Tup α β) := fun _ _ => isTrue rfl
instance : DecidableEq (Rel α β) := fun _ _ => isTrue rfl
instance : DecidableEq (Tab α β) := fun _ _ => isTrue rfl

instance : Ord (Tup α β) := ⟨fun _ _ => .eq⟩
instance : Ord (Rel α β) := ⟨fun _ _ => .eq⟩
instance : Ord (Tab α β) := ⟨fun _ _ => .eq⟩

instance : Hashable (Tup α β) := ⟨fun _ => 0⟩
instance : Hashable (Rel α β) := ⟨fun _ => 0⟩
instance : Hashable (Tab α β) := ⟨fun _ => 0⟩

instance [ToTypList α] [ToTyp β] : ToTyp (Tup α β) :=
  ⟨.prod (ToTypList.typsOf α β)⟩

instance [ToTypList α] [ToTyp β] : ToTyp (Rel α β) :=
  ⟨.set (.prod (ToTypList.typsOf α β))⟩

instance [ToTypList α] [ToTyp β] : ToTyp (Tab α β) :=
  ⟨.bag (.prod (ToTypList.typsOf α β))⟩



/-! ## Positions

A component's position, as a value that knows the component's type. This is what makes projection
*typed*: cvc5 takes an `Array Nat`, whose contents are a runtime value, so a projection built from
one cannot say what it lands at. A `Col` is the same number with its meaning attached, and a `Cols`
spine assembles the result index as it collects positions.

Positions count from zero over `α ++ [β]`, exactly as `tupleProject`'s indices do.
-/

/-- The component a position-zero column has: the head of `α`, or `β` when `α` is empty.

Folding the two cases into one class is what lets a position be written as a numeral. They have
different types, so a macro expanding `col%2` cannot know which terminal to emit; the instances
pick by the shape of `α`, and they do not overlap, so resolution is deterministic.
-/
class ColHead (α : List Type) (β : Type) (γ : outParam Type)

instance : ColHead [] β β := ⟨⟩
instance : ColHead (γ :: αs) β γ := ⟨⟩

/-- The position of a component of type `gamma` in a tuple whose components are `α ++ [β]`.

Carries nothing but the position. Built with `col%`, or with `zero`/`next` directly.
-/
structure Col (α : List Type) (β γ : Type) where
  private mk ::
  private idx : Nat

namespace Col

/-- The first component. -/
def zero [ColHead α β γ] : Col α β γ := ⟨0⟩

/-- The position after the given one, in a tuple with one more component in front. -/
def next (c : Col αs β γ) : Col (α :: αs) β γ := ⟨c.idx + 1⟩

/-- The position as a number, counting from zero over `α ++ [β]`. -/
def toNat (c : Col α β γ) : Nat := c.idx

end Col

/-- Positions to project onto, in order, along with the index they land at.

`last` and `cons` are the only builders, so the positions collected and the components the result
index describes stay in step, and the selection cannot come out empty. A position may appear twice
and they need not increase, so this reorders and duplicates as readily as it selects — exactly what
`tupleProject` does.
-/
structure Cols (α : List Type) (β : Type) (α' : List Type) (β' : Type) where
  private mk ::
  private idxs : Array Nat

namespace Cols

/-- The final position of the selection. -/
def last (c : Col α β β') : Cols α β [] β' := ⟨#[c.idx]⟩

/-- Adds a position in front of the ones collected so far. -/
def cons (c : Col α β γ) (rest : Cols α β α' β') : Cols α β (γ :: α') β' :=
  ⟨#[c.idx] ++ rest.idxs⟩

/-- The positions as numbers, in order. -/
def toArray (cols : Cols α β α' β') : Array Nat := cols.idxs

end Cols

open Lean in
/-- A component's position, written as a numeral: `col%2` is the third component.

Out of range is a type error, there being no `ColHead` instance left to end the chain. Declared at
maximum precedence, so it needs no parentheses as a function argument.
-/
scoped macro:max "col%" n:num : term => do
  let mut col ← `(Col.zero)
  for _ in [0 : n.getNat] do
    col ← `(Col.next $col)
  return col

open Lean in
/-- A selection of positions: `cols% [2, 0]` projects onto the third component then the first.

An element may be any `Col` term, so a named column works — `cols% [dept, 0]` — and a numeral is
shorthand for `col%` of it.
-/
scoped macro:max "cols%" "[" elems:term,+ "]" : term => do
  let elems := elems.getElems
  let col (e : Term) : MacroM Term := do
    if let some n := e.raw.isNatLit? then
      let mut col ← `(Col.zero)
      for _ in [0 : n] do
        col ← `(Col.next $col)
      return col
    else return e
  let mut cols ← `(Cols.last $(← col elems.back!))
  for e in elems.pop.reverse do
    cols ← `(Cols.cons $(← col e) $cols)
  return cols
