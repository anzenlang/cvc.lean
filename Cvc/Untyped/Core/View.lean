/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Untyped.Core.Defs

public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.Core.BVar



/-! # What sort-erased views are built from

A **view** takes a term apart one level: its operator, as a constructor, and its kids. Each theory
has one, generated from its specification beside its constructors (`gen_untyped_view%`) or written
by hand for what no specification describes, and `def.term_view V` gathers the views of every
imported theory into one inductive `V`, with the leaves — values, symbols, bound variables — and a
catch-all. This module holds what those need.

Taking a term apart is pure: its kind, kids and indices are read without `Env`. The only failure is
an ill-formed term, which cvc5 never builds, so a view does not answer an error for it.
-/

namespace Cvc.Untyped public section variable [Ω]

open cvc5 renaming Term → T

/-- An n-ary operator's kids: at least two. -/
abbrev Kids := { ks : Terms // 2 ≤ ks.size }

/-- An n-ary operator's kids, if there are at least two. -/
def Kids.of? (ks : Terms) : Option Kids := if h : 2 ≤ ks.size then some ⟨ks, h⟩ else none

/-- The first of an n-ary operator's kids. -/
def Kids.first (ks : Kids) : Term := ks.val[0]'(by have := ks.property; omega)

/-- An application's arguments: at least one. -/
abbrev Args := { as : Terms // 0 < as.size }

/-- An application's arguments, if there is one. -/
def Args.of? (as : Terms) : Option Args := if h : 0 < as.size then some ⟨as, h⟩ else none

/-- The `i`-th index of a term's operator, as a `Nat`, if its operator is indexed that far. -/
def Term.indexAt? (t : Term) (i : Nat) : Option Nat := do
  let op ← T.getOp? t.toUnsafe
  if h : i < op.getNumIndices then (T.getIntegerValue? (op.get ⟨i, h⟩)).map Int.toNat else none

/-- The views a traversal hands its functions, and how to build one. -/
class TermView (V : outParam Type) where
  /-- Takes a term apart one level. -/
  viewOf : Term → V

end

end Cvc.Untyped
