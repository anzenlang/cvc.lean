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

A typed term is a sort-erased one carrying a phantom Lean index describing its sort. The index is
erased at runtime: `Term α` is definitionally `Untyped.Term`, and the conversions either way are
`id`, so stating a sort costs nothing.

`Cvc.Typed.Term` names both this type and the namespace holding the generated constructors,
so a signature can mention `Term α` without reaching outside the layer.
-/
namespace Cvc.Typed public section variable [Ω]

def3% Term α ← Cvc.Untyped.Term (ofUntypedUnsafe / toUntypedUnsafe)

/-- An array of terms of the sort `α` describes. -/
abbrev Terms (α : Type) := Array (Term α)

namespace Term

/-- Erases its type. -/
def erase (t : Term α) : Untyped.Term := t

/-- Types an untyped term. -/
def ofUntyped' (t : Untyped.Term) (α : Type) [ToTyp α] : Env (Term α) := do
  let srt ← t.getSort
  let srt' ← Srt.of α
  if srt != srt' then
    throwUser s!"cannot type the following term as `{srt'}`, term has sort `{srt}`:\n{t}"
  return t

@[inherit_doc ofUntyped']
abbrev ofUntyped [ToTyp α] (t : Untyped.Term) : Env (Term α) := ofUntyped' t α

/-! ## Substitution

Simultaneous and applied once, as sort-erased — see `Untyped.Term.substitute'`.

A pair's two terms share an index, which is what keeps the result at `α`: replacing a sub-term of
sort `β` by another of sort `β` cannot change the sort of the whole. `heteroSubstitute` relaxes
only *across* pairs, never within one.
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

@[inherit_doc Typed.Term.ofUntyped']
def _root_.Cvc.Untyped.Term.typeCheckAs (t : Untyped.Term) (α : Type) [ToTyp α]
: Env (Term α) := Typed.Term.ofUntyped' t α

@[inherit_doc Untyped.Term.typeCheckAs]
def _root_.Cvc.Untyped.Term.typeCheck [ToTyp α] (t : Untyped.Term)
: Env (Term α) := t.typeCheckAs α

namespace Terms

private def toUnsafe : Terms α → Array cvc5.Term := id
private def ofUnsafe : Array cvc5.Term → Terms α := id

private example (ts : Terms α) : ofUnsafe ts.toUnsafe = ts := rfl

end Terms


/-- Typed `smt!`.

`scoped`, so that `open Cvc.Typed` selects this layer's DSL. It forwards to `smtT!`, which
expands to fully-qualified `Cvc.Typed.Term.…` calls; nothing needs to be in scope.

Opening both layers at once makes the two `smt!` parsers ambiguous — open the one you mean.
-/
scoped syntax "smt! " ppLine group(colGt smtTerm) : term

macro_rules | `(smt! $t:smtTerm) => `(smtT! $t)
