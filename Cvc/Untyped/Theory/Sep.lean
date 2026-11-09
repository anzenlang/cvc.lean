/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt
import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.Core.Solver

public import Cvc.Srt
public import Cvc.Gen.View
public import Cvc.Untyped.Core.View
public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.Core.Solver
public import Cvc.Ext
public import Cvc.Spec.Sep



/-! # Separation logic, sort-erased

The whole theory lives here, the solver functions included: a separation-logic term's
well-formedness depends on the heap a solver declared, not only on its operands.

## The heap is declared, and everything hangs off that

`Solver.declareSepHeap` fixes the heap's location and data sorts, once per solver, and cvc5 checks
nothing else against them: `(pto 1 true)` is built without complaint against a heap of
`Loc × Int` and fails only at check-sat, reporting a type error about `set.union` — cvc5's internal
encoding showing through.

So `declareSepHeap` answers a **handle**, and the two heap-dependent constructors hang off it:

- `Heap.pto`, which checks its operands against the sorts the handle carries;
- `Heap.nil`, which builds `sep.nil` at the heap's location sort rather than at any sort a caller
  might name.

The handle is indexed by the solver that produced it: two solvers of one scope may declare
*different* heaps.

`sepEmp`, `sepStar` and `sepWand` mention no heap sort, so they need no handle. None of these
operators is lifted over nullables.
-/
-- This module inverts the usual layering, a theory module importing `Solver` rather than the other
-- way round; that is the price of keeping the area in one place. There is no nullable lift because
-- `nullable.lift` of a separating conjunction is not something cvc5 gives a meaning to.
namespace Cvc.Untyped public section

namespace Term variable [Ω]

gen_untyped% from Cvc.Spec.Sep
gen_untyped_view% from Cvc.Spec.Sep

end Term



namespace Solver variable [Ω] open cvc5 renaming Solver → S variable (s : Solver)

/-- The heap of a solver, and the sorts it was declared at.

Produced by `declareSepHeap`, and the only way to `Heap.pto` or `Heap.nil`.
-/
structure Heap (solver : Solver) where private mk ::
  /-- Sort of the heap's locations. -/
  loc : Srt
  /-- Sort of the data a location points to. -/
  data : Srt
deriving BEq

/-- Declares the heap's location and data sorts, and answers the handle they are reached through.

cvc5 allows this **once** per solver, and rejects a second call even at the same sorts. It has to
come before any separation-logic constraint: asserting one against an undeclared heap is an error.
-/
def declareSepHeap (loc data : Srt) : Env (Heap s) := do
  runUnsafe' do s.toUnsafe.declareSepHeap loc data
  return ⟨loc, data⟩

namespace Heap variable {s : Solver} (h : Heap s)

/-- The location sort and the data sort, in that order. -/
def sorts : Srt × Srt := (h.loc, h.data)

/-- `sep.nil`, the null location, at the heap's location sort. -/
def nil : Env Term := runUnsafe fun tm => tm.mkSepNil h.loc
-- cvc5's `mkSepNil` takes whatever sort it is given; this cannot answer a `sep.nil` the heap has
-- no use for.

/-- The points-to constraint: `loc` points to `data` in a heap holding nothing else.

The operands are checked against the sorts the heap was declared at, which cvc5 does not do until
check-sat — and then reports as a `set.union` type error naming neither `pto` nor the heap.
-/
def pto (loc data : Term) : Env Term := do
  let locSrt ← loc.getSort
  if locSrt != h.loc then
    throwUser s!"\
      this heap's locations have sort `{h.loc}`, but `{loc}` has sort `{locSrt}`"
  let dataSrt ← data.getSort
  if dataSrt != h.data then
    throwUser s!"\
      this heap's data has sort `{h.data}`, but `{data}` has sort `{dataSrt}`"
  runUnsafe fun tm => tm.mkTerm .SEP_PTO #[loc, data]

end Heap



/-! ## Reading a heap back -/

/-- A formula describing the model's heap, such as `(pto (as @Loc_1 Loc) 0)`; not a value. -/
def getValueSepHeap : s.EnvSat Term := runUnsafe' do s.toUnsafe.getValueSepHeap

/-- A formula giving `sep.nil` in the model, such as `(= (as sep.nil Loc) (as @Loc_0 Loc))`. -/
def getValueSepNil : s.EnvSat Term := runUnsafe' do s.toUnsafe.getValueSepNil
-- cvc5 documents these two as "the term for the heap" and "the term for nil", but both answer a
-- `Bool`-sorted formula.

/-- `getValueSepHeap` in `Env`, not checked to follow a sat answer. -/
def getValueSepHeap! : Env Term := s.getValueSepHeap.toEnv

/-- `getValueSepNil` in `Env`, not checked to follow a sat answer. -/
def getValueSepNil! : Env Term := s.getValueSepNil.toEnv

end Solver
