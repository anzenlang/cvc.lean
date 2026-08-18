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
import all Cvc.Typed.Solver

public import Cvc.Untyped.Theory.Sep
public import Cvc.Typed.Solver
public import Cvc.Ext
public import Cvc.Gen
public import Cvc.Spec.Sep



/-! # Separation logic, typed

The sort-erased module holds the reasoning; this one states it in types. Read
`Cvc.Untyped.Theory.Sep` first.

`Heap` is where the layer earns its keep. Sort-erased it carries the two `Srt`s and checks them at
construction; here it carries the two **Lean types**, so

```lean
def pto (h : s.Heap α β) (loc : Term α) (data : Term β) : Env (Term Bool)
def nil (h : s.Heap α β) : Env (Term α)
```

make a heap mismatch a *type* error, and `nil` comes out at the location index with nothing to
ascribe.

**A handle fits here where it did not fit datatypes.** The objection there was that a handle's
index has no `ToTyp`, so it cannot go where one is required — inside `Set α`, `declareConst α`, a
tuple component. A heap is never a term's sort: `sep.nil` is a term of the *location* sort, which
is an ordinary Lean type with an ordinary `ToTyp`. So nothing ever asks for `ToTyp (Heap α β)`, and
the objection does not arise.

`Heap` is a `structure` wrapping the sort-erased handle rather than an abbreviation of it. An
abbreviation unfolds, and dot notation would then find `Untyped.Solver.Heap.pto` — which takes
sort-erased terms, and would accept them, a typed term being definitionally its sort-erased one.
The wrapper is what keeps `h.pto` meaning the typed one. `Proof` needed the same care.
-/
namespace Cvc.Typed public section

namespace Term variable [Ω]

open Cvc renaming Untyped.Term → T

gen_typed% from Cvc.Spec.Sep

end Term



namespace Solver variable [Ω] open Cvc renaming Untyped.Solver → U

/-- The heap of a solver, at the Lean types of its locations and its data.

Produced by `declareSepHeap`, and the only way to `Heap.pto` or `Heap.nil`. Indexed by its solver,
as the sort-erased handle is, and by the two types the sort-erased one carries as `Srt`s.
-/
structure Heap (solver : Solver) (α β : Type) where private mk ::
  private toUntyped : U.Heap solver

variable (s : Solver)

@[inherit_doc U.declareSepHeap]
def declareSepHeap (α β : Type) [ToTyp α] [ToTyp β] : Env (Heap s α β) := do
  let loc ← Srt.of α
  let data ← Srt.of β
  return ⟨← U.declareSepHeap s loc data⟩

namespace Heap variable {s : Solver} (h : Heap s α β)

/-- The location sort and the data sort, in that order. -/
def sorts : Srt × Srt := h.toUntyped.sorts

@[inherit_doc U.Heap.nil]
def nil : Env (Term α) := h.toUntyped.nil

/-- The points-to constraint: `loc` points to `data` in a heap holding nothing else.

The operands are the heap's own indices, so the mismatch the sort-erased version has to check is
not expressible here.
-/
def pto (loc : Term α) (data : Term β) : Env (Term Bool) :=
  h.toUntyped.pto loc.erase data.erase

end Heap



/-! ## Reading a heap back

Both answer a `Bool`-sorted formula characterizing the model's heap rather than a value, so both
are `Term Bool` whatever the heap's indices — see the sort-erased module.
-/

@[inherit_doc U.getValueSepHeap]
def getValueSepHeap : EnvSat (Term Bool) := U.getValueSepHeap s

@[inherit_doc U.getValueSepNil]
def getValueSepNil : EnvSat (Term Bool) := U.getValueSepNil s

end Solver
