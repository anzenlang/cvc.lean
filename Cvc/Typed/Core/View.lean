/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs

public import Cvc.Typed.Core.Defs
public import Cvc.Untyped.Core.View
public import Cvc.Typed.Core.BVar
public import Cvc.Types.Denote



/-! # What typed views are built from

A typed view takes a term of sort `τ` apart one level, with its kids typed. Each theory's is
indexed by the sort it takes apart — `View.Arith : Typ → Type` — so that matching on an operator
refines the sort, and a kid whose sort the operator does not fix is a `Term σ.Denote` for a
`σ : Typ` it carries. It is built from the theory's sort-erased view, converting constructor by
constructor: the sort-erased view has read the kind, the kids and the indices, and the typed one
adds the sorts and the facts about them. `def.term_view V`, under `open Cvc.Typed`, gathers them
into `V : Typ → Type`. This module holds what those need.

A typed view reads sorts, which the library does in `Env`. A node whose sort no `Typ` describes,
or whose operator the typed view cannot type, is a typed view's `none`, and the aggregate's
`other`.
-/

namespace Cvc.Typed public section variable [Ω]

/-- The kids of an n-ary operator: at least two. -/
abbrev Kids (α : Type) := { ks : Array (Term α) // 2 ≤ ks.size }

namespace View

/-- A sort-erased term at an index, unchecked: what a typed view does with a kid whose sort cvc5
has already checked against the operator's signature. -/
def reindex (t : Untyped.Term) : Term α := t

/-- Sort-erased kids at an index, unchecked, keeping their arity. -/
def kids (ks : Untyped.Kids) : Kids α := ⟨ks.val.map reindex, by simpa using ks.property⟩

/-- A term's sort as a `Typ`, or `none` if no `Typ` describes it. -/
def typOf? (t : Untyped.Term) : Env (Option Typ) :=
  tryCatch (do return some (← (← t.getSort).toTyp)) fun _ => return none

/-- A proof of `p`, if it holds: what a typed view stores of a fact cvc5 guarantees. -/
def proof? (p : Prop) [Decidable p] : Option (PLift p) := if h : p then some ⟨h⟩ else none

end View

/-- The views a typed traversal hands its functions, one per sort, and how to build one. -/
class ViewFamily (V : outParam (Typ → Type)) where
  /-- Takes a term apart one level, at its sort. -/
  viewOf : (τ : Typ) → Term τ.Denote → Env (V τ)

end

end Cvc.Typed
