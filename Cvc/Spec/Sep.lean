/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Separation logic specification

Only the three kinds that mention **no heap sort** are specified here, and they are all `Bool`:
`sep.emp`, and the two connectives. cvc5 marks the whole family experimental.

`SEP_PTO` and `SEP_NIL` are deliberately absent. Both are only meaningful against the heap that
`Solver.declareSepHeap` declares — a `pto` whose operands are not the heap's location and data
sorts is accepted by cvc5 at construction and rejected at check-sat, with an error naming
`set.union` rather than `pto`. So they hang off the handle `declareSepHeap` answers instead, in
`Cvc.{Untyped,Typed}.Theory.Sep`, where the sorts are known and can be checked.
-/
namespace Cvc public section

/-- The empty heap. -/
op% sepEmp : bool := SEP_EMP tm mkSepEmp

/-- Separating conjunction: the heap splits in two, one part satisfying each side. -/
op% sepStar (lft rgt : bool) : bool := SEP_STAR nary

/-- Separating implication, the magic wand. -/
op% sepWand (lft rgt : bool) : bool := SEP_WAND
