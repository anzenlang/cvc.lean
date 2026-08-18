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
import all Cvc.Untyped.Solver

public import Cvc.Srt
public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.Solver
public import Cvc.Ext
public import Cvc.Gen
public import Cvc.Spec.Sep



/-! # Separation logic, sort-erased

**The whole theory lives here**, the solver functions included, because separation logic is the one
area where a term's well-formedness is a property of *solver state* rather than of its operands.
That inverts the usual layering — a theory module importing `Solver` rather than the other way
round — and it is the price of keeping the area in one place.

## The heap is declared, and everything hangs off that

`Solver.declareSepHeap` fixes the heap's location and data sorts, once per solver, and cvc5 checks
nothing else against them: `(pto 1 true)` is built without complaint against a heap of
`Loc × Int` and fails only at check-sat, reporting a type error about `set.union` — cvc5's internal
encoding showing through.

So `declareSepHeap` answers a **handle**, and the two heap-dependent constructors hang off it:

- `Heap.pto`, which checks its operands against the sorts the handle carries;
- `Heap.nil`, which builds `sep.nil` at the heap's location sort rather than at any sort a caller
  might name.

The handle is indexed by the solver that produced it, as `Proof` is, because a heap belongs to one
solver: two solvers sharing a term manager may declare *different* heaps, and cvc5 accepts that.
A term built for one is meaningless to the other.

`sepEmp`, `sepStar` and `sepWand` mention no heap sort, so they are ordinary generated constructors
and need no handle.

## Not lifted over nullables

There is no `Nullable/Sep.lean`. `nullable.lift` of a separating conjunction is not something cvc5
gives a meaning to, and the operators are `Bool`-valued anyway.
-/
namespace Cvc.Untyped public section

namespace Term variable [Ω]

gen_untyped% from Cvc.Spec.Sep

end Term



namespace Solver variable [Ω] open cvc5 renaming Solver → S

/-- The heap of a solver, and the sorts it was declared at.

Produced by `declareSepHeap`, and the only way to `Heap.pto` or `Heap.nil`. Indexed by its solver
because a heap belongs to one: two solvers may declare different heaps, and a location of one is
not a location of the other.
-/
structure Heap (solver : Solver) where private mk ::
  /-- Sort of the heap's locations. -/
  loc : Srt
  /-- Sort of the data a location points to. -/
  data : Srt
deriving BEq

variable (s : Solver)

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

/-- `sep.nil`, the null location, at the heap's location sort.

cvc5's `mkSepNil` takes whatever sort it is given, so this is the only spelling that cannot answer
a `sep.nil` the heap has no use for.
-/
def nil : Env Term := runUnsafe fun tm => tm.mkSepNil h.loc

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



/-! ## Reading a heap back

Both of these answer a `Bool`-sorted *formula* characterizing the model's heap, not a value of the
heap or of `sep.nil` — cvc5's own docstrings ("the term for the heap", "the term for nil") read
otherwise. On a model of `(pto x v)` they give something like `(pto (as @Loc_1 Loc) 0)` and
`(= (as sep.nil Loc) (as @Loc_0 Loc))`.
-/

@[inherit_doc S.getValueSepHeap]
def getValueSepHeap : EnvSat Term := runUnsafe' do s.toUnsafe.getValueSepHeap

@[inherit_doc S.getValueSepNil]
def getValueSepNil : EnvSat Term := runUnsafe' do s.toUnsafe.getValueSepNil

end Solver
