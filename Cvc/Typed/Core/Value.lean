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
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.Core.Value
import all Cvc.Typed.Core.Defs

public import Cvc.Srt
public import Cvc.Untyped.Core.Value
public import Cvc.Typed.Core.Defs



/-! # Values, typed

The same two directions as the sort-erased layer, stated at an index: `ValueToTerm α` builds a
`Term α` from an `α`, `TermToValue α` reads an `α` back out of one. The classes are this layer's
own — a typed term is opaque to a user who imports only this layer, so a sort-erased instance
would not apply to it.

Reading a term's own structure needs no index and is inherited unchanged, except that the *sort* of
a term is what its index already describes, so the readers below narrow the terms they accept.
-/
namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## The classes -/

/-- Reads the value a constant term denotes, as a Lean `α`. -/
class TermToValue (α : Type) where
  /-- Reads the value a constant term denotes. -/
  termToValue : [Ω] → Term α → Env α

-- no `TermToValue (Term α)`: `TermToValue β` reads a `Term β`, so at `β := Term α` it would have to
-- read a `Term (Term α)`. An index describes a sort, and a term is not one.

/-- Builds the constant term denoting a Lean `α`. -/
class ValueToTerm (α : Type) where
  /-- Builds the constant term denoting a value. -/
  valueToTerm : [Ω] → α → Env (Term α)

/-- A Lean type usable as a sort, in both directions. -/
class abbrev SrtLike (α : Type) (β : Type := α) := ToTyp α, TermToValue α, ValueToTerm α

/-- The sort-erased conversion an instance of this layer's class induces.

`reducible` so that instance resolution sees through it where a sort-erased conversion is what a
delegation needs.
-/
@[reducible]
def TermToValue.toUntyped [A : TermToValue α] : Untyped.TermToValue α := ⟨A.termToValue⟩

@[inherit_doc TermToValue.toUntyped, reducible]
def ValueToTerm.toUntyped [A : ValueToTerm α] : Untyped.ValueToTerm α := ⟨A.valueToTerm⟩

namespace Term

/-- The constant term denoting a value. -/
def mkValue [A : ValueToTerm α] : (value : α) → Env (Term α) := A.valueToTerm

@[inherit_doc mkValue]
def mkValueAs (α : Type) [ValueToTerm α] : (value : α) → Env (Term α) := mkValue

/-- The value a constant term denotes. -/
def getValue [A : TermToValue α] : Term α → Env α := A.termToValue

@[inherit_doc getValue]
def getValueAs (α : Type) [TermToValue α] : Term α → Env α := getValue



/-! ## Reading a term's own structure

These hold whatever a term's index, so they take any of them. Sub-terms are sort-erased: nothing
about a term's index says what its children's indices are.

The readers that *are* tied to an index — `getIntValue`, `getBitVecValue`, and the rest — live in
their own theory, beside the constructor that builds what they read.
-/

/-- The sort of a term.

An index describes a sort, so this is `Srt.of α` — reading it off the term is the way to see
whether the two agree.
-/
def getSort (term : Term α) : Env Srt := T.getSort term

@[inherit_doc T.getId]
def getId (term : Term α) : Res Nat := T.getId term

@[inherit_doc T.getKind]
def getKind (term : Term α) : Res Kind := T.getKind term
@[inherit_doc getKind]
def getKind? (term : Term α) : Option Kind := T.getKind? term

@[inherit_doc T.hasSymbol]
def hasSymbol (term : Term α) : Res Bool := T.hasSymbol term
@[inherit_doc T.getSymbol]
def getSymbol (term : Term α) : Res String := T.getSymbol term

@[inherit_doc T.getKids]
def getKids (term : Term α) : Untyped.Terms := T.getKids term

@[inherit_doc T.getSizedKids]
def getSizedKids (term : Term α) (size : Nat)
: Env {kids : Untyped.Terms // kids.size = size} := T.getSizedKids term size

end Term
