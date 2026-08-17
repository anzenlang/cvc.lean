/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Term.Defs

public import Cvc.Srt
public import Cvc.Untyped.Term.Defs



/-! # Values, sort-erased

Two classes relate a Lean type to the terms that denote its values, in the two directions:
`ValueToTerm α` builds a constant term from an `α`, `TermToValue α` reads an `α` back out of one.
`SrtLike` bundles them with `ToTyp`, which is what a type needs to be usable as a sort at all.

Only the *readers* live here — they need nothing but the term. A writer needs its theory's
constructor, so each instance is registered in the theory module that can build it, and a consumer
that imports one theory does not compile the others.
-/
namespace Cvc.Untyped public section variable [Ω]

open cvc5 renaming Term → T



/-! ## The classes -/

/-- Reads the value a constant term denotes, as a Lean `α`. -/
class TermToValue (α : Type) where
  /-- Reads the value a constant term denotes. -/
  termToValue : Term → Env α

namespace TermToValue
instance : TermToValue Term := ⟨pure⟩
end TermToValue

/-- Builds the constant term denoting a Lean `α`. -/
class ValueToTerm (α : Type) where
  /-- Builds the constant term denoting a value. -/
  valueToTerm : α → Env Term

namespace ValueToTerm
instance : ValueToTerm Term := ⟨pure⟩
end ValueToTerm

/-- A Lean type usable as a sort, in both directions. -/
class abbrev SrtLike (α : Type) := ToTyp α, TermToValue α, ValueToTerm α

namespace Term

/-- The constant term denoting a value. -/
def mkValue [A : ValueToTerm α] : (value : α) → Env Term := A.valueToTerm

@[inherit_doc mkValue]
def mkValueAs (α : Type) [A : ValueToTerm α] : (value : α) → Env Term := mkValue

/-- The value a constant term denotes. -/
def getValue [A : TermToValue α] : Term → Env α := A.termToValue

@[inherit_doc getValue]
def getValueAs (α : Type) [A : TermToValue α] : Term → Env α := getValue



/-! ## Reading a term's own structure

These say what a term *is*, as opposed to what value it denotes, and they hold whatever its sort.
Reconstructing a container value goes through them: an SMT bag or array is a spine of applications,
so reading one back means walking its kind and children.

The readers that *are* tied to a sort — `getIntValue`, `getBitVecValue`, and the rest — live in
their own theory, beside the constructor that builds what they read.
-/

/-- The sort of a term. -/
def getSort (term : Term) : Env Srt := do
  let srt ← T.getSort term.toUnsafe |>.mapError Error.ofUnsafe
  return by unfold Srt ; exact srt

@[inherit_doc T.getId]
def getId (term : Term) : Res Nat := T.getId term.toUnsafe |>.mapError Error.ofUnsafe

@[inherit_doc T.getKind]
def getKind (term : Term) : Res Kind := T.getKind term.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getKind]
def getKind? (term : Term) : Option Kind := T.getKind? term.toUnsafe

@[inherit_doc T.hasSymbol]
def hasSymbol (term : Term) : Res Bool := T.hasSymbol term.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc T.getSymbol]
def getSymbol (term : Term) : Res String := T.getSymbol term.toUnsafe |>.mapError Error.ofUnsafe

/-- The sub-terms of a term. -/
def getKids (term : Term) : Terms :=
  let kids : Array cvc5.Term := T.getChildren term.toUnsafe
  kids

/-- The sub-terms of a term, failing unless there are exactly `size` of them. -/
def getSizedKids (term : Term) (size : Nat) : Env {kids : Terms // kids.size = size} := do
  let kids := term.getKids
  if h : kids.size = size then return ⟨kids, h⟩ else
    throwUser s!"expected {size} kid(s), got {kids.size} in term `{term}` of kind {term.getKind?}"
