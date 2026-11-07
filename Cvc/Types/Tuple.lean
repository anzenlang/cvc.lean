/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt



/-! # Product-indexed tuples

A Lean product indexes a tuple: `α × β × γ` is one three-component tuple, as products flatten to
the right, while `(α × β) × γ` has two components, the first a tuple. `OneTuple α` is the
one-component tuple. Relations and tables use the list-shaped `Tup` of `Cvc.Types.Relation`.
-/

namespace Cvc public section


namespace Typ

/-- Whether a sort is a single tuple component rather than a tuple of its own.

A product cannot be a tuple's *last* component: its own components would flatten into the tuple.
-/
abbrev isFlat : Typ → Bool
  | prod _ => false
  | bool | int | real | string | regex | roundingMode
  | bitVec _ | float _ _ | finiteField _ | arrayTo _ _
  | bag _ | set _ | seq _ | nullable _ | record _
  | datatype _ | function _ _ | uninterpreted _ => true

end Typ

namespace Srt

/-- The tuple `Typ` of `α` then `β`, flattening a tuple `β` into its components. -/
@[expose]
def prod (α : Typ) : (β : Typ) → Typ
  | .prod args => .prod (α :: args)
  | β => .prod [α, β]
-- `expose`d so the body crosses a plain `import`: the typed tuple constructor checks its last
-- component's index by reduction, and cannot if this stays opaque.

instance [A : ToTyp α] [B : ToTyp β] : ToTyp (α × β) where
  typ := Srt.prod A.typ B.typ

end Srt



/-- Lexicographic order on pairs, so that a set, bag or array index of tuples can be written.

A global instance: importing the library brings it into scope.
-/
instance (priority := low) instOrdProd [Ord α] [Ord β] : Ord (α × β) := lexOrd
-- Core provides no `Ord (α × β)`, leaving `lexOrd` a function so that the choice of order stays the
-- user's. Making it an instance fixes that choice, and the choice is not idle: the comparator is a
-- *type index* on `Std.TreeSet`/`Std.TreeMap`, so `Set (α × β)` means a different type under a
-- different order. Lexicographic is the only order a tuple has a canonical claim to, and without an
-- instance a set of tuples cannot be written at all.

/-- A tuple of one component, denoting the one-component SMT tuple sort `(Tuple α)`.

Like any product it nests as a *first* component and flattens as a last: `OneTuple α × β` is
`(Tuple (Tuple α) β)` while `α × OneTuple β` is `(Tuple α β)`.
-/
structure OneTuple (α : Type) where
  /-- The component. -/
  value : α
deriving DecidableEq, Ord, Hashable

namespace OneTuple

instance [A : ToTyp α] : ToTyp (OneTuple α) where
  typ := .prod [A.typ]

end OneTuple
