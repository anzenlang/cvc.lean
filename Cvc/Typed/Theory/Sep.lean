/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs
import all Cvc.Untyped.Theory.Sep
import all Cvc.Typed.Core.Solver

public import Cvc.Untyped.Theory.Sep
public import Cvc.Gen.TypedView
public import Cvc.Typed.Core.View
public import Cvc.Typed.Core.Solver
public import Cvc.Ext
public import Cvc.Spec.Sep



/-! # Separation logic, typed

A solver's heap is declared once, at the Lean types of its locations and data. The two constructors
that depend on it hang off the handle `declareSepHeap` answers, so a location or a datum of the
wrong type does not compile:

```lean
let h ← s.declareSepHeap Int Int
s.assert (← h.pto x y)     -- `x y : Term Int`
let n ← h.nil              -- `n : Term Int`
```

`sepEmp`, `sepStar` and `sepWand` need no heap. `getValueSepHeap` and `getValueSepNil` describe the
model's heap as formulas.
-/
-- A handle fits here where it did not fit datatypes: a handle's index has no `ToTyp`, so it cannot
-- go where one is required. But a heap is never a term's sort — `sep.nil` is a term of the
-- location sort — so nothing ever asks for `ToTyp (Heap α β)`.
--
-- `Heap` is a structure wrapping the sort-erased handle rather than an abbreviation of it: an
-- abbreviation unfolds, and dot notation would then find `Untyped.Solver.Heap.pto`, which would
-- accept typed terms, a typed term being definitionally its sort-erased one. `Proof` needed the
-- same care.
namespace Cvc.Typed public section

namespace Term variable [Ω]

open Cvc renaming Untyped.Term → T

gen_typed% from Cvc.Spec.Sep
gen_typed_view% from Cvc.Spec.Sep

end Term



namespace Solver variable [Ω] open Cvc renaming Untyped.Solver → U

/-- The heap of a solver, at the Lean types of its locations and its data.

Produced by `declareSepHeap`, and the only way to `Heap.pto` or `Heap.nil`.
-/
structure Heap (solver : Solver) (α β : Type) where private mk ::
  private untyped : U.Heap solver

/-- The sort-erased heap it wraps, which carries `α` and `β` as `Srt`s; free. -/
def Heap.toUntyped {solver : Solver} (h : Heap solver α β) : U.Heap solver := h.untyped

@[inherit_doc Heap.toUntyped]
abbrev Heap.erase {solver : Solver} (h : Heap solver α β) : U.Heap solver := h.toUntyped

/-- Types a sort-erased heap at locations `α` and data `β`, checking its two sorts against theirs.

`toTyped` infers `α` and `β` from the expected type; `typeCheckAs` and `typeCheck` are the same two
functions under the names that say what they do.
-/
def _root_.Cvc.Untyped.Solver.Heap.toTypedAs (α β : Type) [ToTyp α] [ToTyp β] {solver : Solver}
  (h : U.Heap solver)
: Env (Heap solver α β) := do
  let (loc, data) := h.sorts
  let loc' ← Srt.of α
  let data' ← Srt.of β
  if loc != loc' then
    throwUser s!"cannot type this heap's locations as `{loc'}`, they have sort `{loc}`"
  if data != data' then
    throwUser s!"cannot type this heap's data as `{data'}`, it has sort `{data}`"
  return ⟨h⟩

@[inherit_doc Untyped.Solver.Heap.toTypedAs]
def _root_.Cvc.Untyped.Solver.Heap.toTyped [ToTyp α] [ToTyp β] {solver : Solver}
  (h : U.Heap solver)
: Env (Heap solver α β) := h.toTypedAs α β

@[inherit_doc Untyped.Solver.Heap.toTypedAs]
abbrev _root_.Cvc.Untyped.Solver.Heap.typeCheckAs := @Untyped.Solver.Heap.toTypedAs

@[inherit_doc Untyped.Solver.Heap.toTypedAs]
abbrev _root_.Cvc.Untyped.Solver.Heap.typeCheck := @Untyped.Solver.Heap.toTyped

variable (s : Solver)

@[inherit_doc U.declareSepHeap]
def declareSepHeap (α β : Type) [ToTyp α] [ToTyp β] : Env (Heap s α β) := do
  let loc ← Srt.of α
  let data ← Srt.of β
  return ⟨← U.declareSepHeap s loc data⟩

namespace Heap variable {s : Solver} (h : Heap s α β)

/-- The location sort and the data sort, in that order. -/
def sorts : Srt × Srt := h.untyped.sorts

@[inherit_doc U.Heap.nil]
def nil : Env (Term α) := h.untyped.nil

/-- The points-to constraint: `loc` points to `data` in a heap holding nothing else.

The operands are the heap's own indices, so the mismatch the sort-erased version has to check is
not expressible here.
-/
def pto (loc : Term α) (data : Term β) : Env (Term Bool) :=
  h.untyped.pto loc.erase data.erase

end Heap



/-! ## Reading a heap back

Both answer a formula describing the model's heap rather than a value, so both are `Term Bool`
whatever the heap's types.
-/

@[inherit_doc U.getValueSepHeap]
def getValueSepHeap : s.EnvSat (Term Bool) := U.getValueSepHeap s

@[inherit_doc U.getValueSepNil]
def getValueSepNil : s.EnvSat (Term Bool) := U.getValueSepNil s

@[inherit_doc U.getValueSepHeap!]
def getValueSepHeap! : Env (Term Bool) := U.getValueSepHeap! s

@[inherit_doc U.getValueSepNil!]
def getValueSepNil! : Env (Term Bool) := U.getValueSepNil! s

end Solver
