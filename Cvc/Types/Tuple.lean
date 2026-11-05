/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt



namespace Cvc public section


namespace Typ

/-- Whether a sort is a single tuple component rather than a tuple of its own.

`Srt.prod` flattens to the right, so a product cannot be a tuple's *last* component: its own
components would flatten into the tuple being built. This is what the typed tuple constructor
checks.
-/
abbrev isFlat : Typ → Bool
  | prod _ => false
  | bool | int | real | string | regex | roundingMode
  | bitVec _ | float _ _ | finiteField _ | arrayTo _ _
  | bag _ | set _ | seq _ | nullable _ | record _
  | datatype _ | function _ _ | uninterpreted _ => true

end Typ

namespace Srt

/-- The product of two sorts, flattening to the right.

`expose`d so the body crosses a plain `import`: the typed tuple constructor checks its last
component's index by reduction, and cannot if this stays opaque.
-/
@[expose]
def prod (α : Typ) : (β : Typ) → Typ
  | .prod args => .prod (α :: args)
  | β => .prod [α, β]

instance [A : ToTyp α] [B : ToTyp β] : ToTyp (α × β) where
  typ := Srt.prod A.typ B.typ

end Srt



/-- Lexicographic order on a pair, needed for a tuple index to sit inside a container.

A relation is a `Set (Tuple …)` and a table a `Bag (Tuple …)`, so a tuple index has to be ordered
before either can be spelled — and core provides no `Ord (α × β)`, leaving `lexOrd` as a function
rather than an instance so that the choice of order stays the user's.

Making it an instance here fixes that choice, and the choice is not idle: the comparator is a
*type index* on `Std.TreeSet`/`Std.TreeMap`, so `Set (α × β)` means a different type under a
different order. Lexicographic is the only order a tuple has a canonical claim to, and the
alternative — no instance — makes relations unspellable.
-/
instance instOrdProd [Ord α] [Ord β] : Ord (α × β) := lexOrd

/-- A tuple of one component, denoting the one-component SMT tuple sort.

`α × β` describes two components or more, so nothing else in *this* encoding denotes `(Tuple α)`.

The relation API no longer needs it — `Rel [] α` is the unary relation under the list-shaped index
of `Types/Relation.lean`, which is the encoding to prefer for anything tuple-shaped. This stays for
the product-indexed tuple API.

It is a product to `Typ` like any other, so it nests as a *first* component and flattens as a
last: `OneTuple α × β` is `(Tuple (Tuple α) β)` while `α × OneTuple β` is `(Tuple α β)`.
-/
structure OneTuple (α : Type) where
  value : α
deriving DecidableEq, Ord, Hashable

namespace OneTuple

instance [A : ToTyp α] : ToTyp (OneTuple α) where
  typ := .prod [A.typ]

end OneTuple
