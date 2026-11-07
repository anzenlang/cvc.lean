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

public import Cvc.Srt
public import Cvc.Types.Tuple
public import Cvc.Untyped.Core.Value
-- a tuple sort is a datatype, and selecting a component is its selector: `tupleSelect` needs the
-- reflection accessors and `applySelector`
public import Cvc.Untyped.Theory.Datatype



/-! # Tuples, sort-erased

`mkTuple` builds a tuple, `tupleSelect` (with `fst` and `snd`) reads one component, and
`tupleProject` answers a **tuple** of the components selected: projecting a single index gives a
one-component tuple, not that component.
-/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T



/-- The tuple whose components are the given terms, in order. -/
def mkTuple (terms : Terms) : Env Term :=
  runUnsafe fun tm => tm.mkTuple terms

/-- The tuple of the components at the given indices, in the order given.

Indices count from zero. They need be neither increasing nor distinct, so this reorders and
duplicates as well as it selects: projecting `#[2, 0]` out of `(Tuple Int Bool Real)` gives
`(Tuple Real Int)`.
-/
def tupleProject (indices : Array Nat) (tuple : Term) : Env Term :=
  runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .TUPLE_PROJECT indices) #[tuple]

/-- The component at the given index, at that component's own sort.

Unlike `tupleProject #[1]`, which answers `(Tuple Bool)` on a `(Tuple Int Bool String)`, this
answers `Bool`.
-/
def tupleSelect (idx : Nat) (tuple : Term) : Env Term := do
  let srt ← tuple.getSort
  unless srt.isTuple do
    throwUser s!"cannot select a component of a term of sort `{srt}`, which is not a tuple"
  let dt ← srt.getDatatype
  if h₀ : 0 < dt.countCtors then
    let ctor := dt.getCtorAt ⟨0, h₀⟩
    if h : idx < ctor.countSelectors then
      applySelector (← (ctor.getSelectorAt ⟨idx, h⟩).getTerm) tuple
    else
      throwUser
        s!"sort `{srt}` has {ctor.countSelectors} component(s), so there is none at index {idx}"
  else
    throwInternal s!"tuple sort `{srt}` has no constructor"
-- There is no kind for it. A tuple sort *is* a datatype — one constructor, one selector per
-- component — so selection is the datatype selector, and cvc5 prints the result as
-- `((_ tuple.select i) t)`.

/-- A tuple's first component. -/
abbrev fst (t : Term) : Env Term := t.tupleSelect 0

/-- A tuple's second component. -/
abbrev snd (t : Term) : Env Term := t.tupleSelect 1


/-! ## Values -/

@[inherit_doc T.isTupleValue]
def isTupleValue (term : Term) : Bool := T.isTupleValue term.toUnsafe

/-- The components a constant tuple term denotes, failing if it denotes none. -/
def getTupleValue (term : Term) : Res Terms := do
  let components : Terms ← T.getTupleValue term.toUnsafe |>.mapError Error.ofUnsafe
  return components
