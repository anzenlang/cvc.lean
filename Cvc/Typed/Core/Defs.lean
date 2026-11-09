/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core.Defs
public import Cvc.Ext

public import Cvc.Untyped.Core

import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.Core



/-! # The typed term type, and this layer's `smt!` entry point

A typed term is a sort-erased one carrying a Lean index describing its sort. The index exists only
at compile time: `Term α` is definitionally `Untyped.Term`, so going down to a sort-erased term is
free, and going up checks the term's sort once.
-/
namespace Cvc.Typed public section variable [Ω]

/-- A cvc5 term whose sort is the one the Lean type `α` denotes.

`Term Int`, `Term (Set Bool)` and `Term (Int → Bool)` are terms of the SMT-LIB sorts `Int`,
`(Set Bool)` and `(-> Int Bool)`; a Lean type denotes a sort through its `ToTyp` instance. Every
constructor states its sorts through the index, so a sort mistake is a Lean type error rather than
a cvc5 error at runtime, and a value read out of a model comes back as an `α`.

The index is phantom: at runtime a `Term α` is exactly a `Cvc.Untyped.Term`. `toUntyped` (or
`erase`) goes down for free, and `Cvc.Untyped.Term.toTyped` (or `typeCheck`) goes up by checking
the term's sort.
-/
def3% Term α ← Cvc.Untyped.Term (ofUntypedUnsafe / toUntypedUnsafe)

/-- An array of terms of the sort `α` describes. -/
abbrev Terms (α : Type) := Array (Term α)

namespace Term

/-- The sort-erased term it is, for free: the index is forgotten, nothing is checked. -/
def toUntyped (t : Term α) : Untyped.Term := t

@[inherit_doc toUntyped]
abbrev erase := @toUntyped

instance : CoeDep (Term α) t Untyped.Term := ⟨t.erase⟩

/-- Types a sort-erased term at `α`, failing if its sort is not `α`'s. -/
def ofUntypedAs (α : Type) [ToTyp α] (t : Untyped.Term) : Env (Term α) := do
  let srt ← t.getSort
  let srt' ← Srt.of α
  if srt != srt' then
    throwUser s!"cannot type the following term as `{srt'}`, term has sort `{srt}`:\n{t}"
  return t

@[inherit_doc ofUntypedAs]
abbrev ofUntyped [ToTyp α] (t : Untyped.Term) : Env (Term α) := ofUntypedAs α t

/-- Re-indexes a term at another Lean type of the same sort, for free.

The two indices must have the same `Typ`, which is checked at compile time. This is how a term a
view hands over, indexed by a `Typ.Denote` that does not reduce, is moved to the index you work
with.
-/
def cast [ToTyp α] [ToTyp β] (t : Term α)
  (_sameSort : Typ.of α = Typ.of β := by
    first | rfl | fail "cannot cast: the two types index different sorts")
: Term β := t
-- Sound because a term's sort is determined by its index's `Typ`: two Lean types with the same
-- `Typ` index the same terms. A `Typ.Denote` fails to reduce over a sort variable, or at the
-- stand-in `Sorted` of a declared sort.

/-! ## Substitution

Simultaneous and applied once, as in the sort-erased layer (`Untyped.Term.substitute'`). The two
terms of a pair share an index, so the result keeps the sort of the original term;
`heteroSubstitute` lets the pairs differ from one another.
-/

/-- Simultaneously replaces each `src[i]` by `tgt[i]` throughout `t`.

Sources and targets share the index `β`, so the result is still a `Term α`. `valid` is cvc5's
requirement that the two arrays be a 1:1 mapping.
-/
def substitute'
  (t : Term α) (src tgt : Terms β)
  (valid : src.size = tgt.size := by
    (try grind) <;> fail "failed to prove there are as many replacements as sub-terms")
: Env (Term α) :=
  t.erase.substitute' src tgt valid

/-- Simultaneously replaces the first of each pair by the second throughout `t`.

Every pair is at one index `β`. Use `heteroSubstitute` to replace terms of several sorts at once.
-/
def substitute (t : Term α) (terms : Array (Term β × Term β)) : Env (Term α) :=
  t.erase.substitute terms

/-- `substitute` where the pairs need not share an index, only agree within each pair. -/
def heteroSubstitute (t : Term α) (terms : Array ((β : Type) × Term β × Term β)) : Env (Term α) :=
  let terms := terms.map fun ⟨_, src, tgt⟩ => (src.erase, tgt.erase)
  t.erase.substitute terms

end Term

/-- Types a sort-erased term at `α`, checking its sort against `α`'s.

`toTyped` infers `α` from the expected type; `typeCheckAs` and `typeCheck` are the same two
functions under the names that say what they do.
-/
def _root_.Cvc.Untyped.Term.toTypedAs (α : Type) [ToTyp α] (t : Untyped.Term)
: Env (Term α) := Typed.Term.ofUntypedAs α t

@[inherit_doc Untyped.Term.toTypedAs]
def _root_.Cvc.Untyped.Term.toTyped [ToTyp α] (t : Untyped.Term)
: Env (Term α) := t.toTypedAs α

@[inherit_doc Untyped.Term.toTypedAs]
abbrev _root_.Cvc.Untyped.Term.typeCheckAs := @Untyped.Term.toTypedAs

@[inherit_doc Untyped.Term.toTypedAs]
abbrev _root_.Cvc.Untyped.Term.typeCheck := @Untyped.Term.toTyped

namespace Terms

private def toUnsafe : Terms α → Array cvc5.Term := id
private def ofUnsafe : Array cvc5.Term → Terms α := id

private example (ts : Terms α) : ofUnsafe ts.toUnsafe = ts := rfl

end Terms


/-- A typed term in notation close to Lean's, as an `Env (Term α)`: `smt! x + 1 ≤ y`.

Available under `open Cvc.Typed`; it accepts the notations of the theories imported. Opening both
layers makes `smt!` ambiguous, so open the one you mean.
-/
scoped syntax "smt! " ppLine group(colGt smtTerm) : term

macro_rules | `(smt! $t:smtTerm) => `(smtT! $t)
