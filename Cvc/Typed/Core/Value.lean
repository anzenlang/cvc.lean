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

`ValueToTerm α` builds a `Term α` from an `α`, and `TermToValue α` reads an `α` back out of one.
Instances bridge to and from the sort-erased classes, so a type with conversions in either layer
works in both.

The readers of a term's own structure — its sort, kind, symbol and children — take a term at any
index; the readers tied to a sort live in that sort's theory.
-/
namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## The classes -/

/-- Reads the value a constant term denotes, as a Lean `α`. -/
class TermToValue (α : Type) where
  /-- Reads the value a constant term denotes. -/
  termToValue : [Ω] → Term α → Env α
-- This layer's own class rather than the sort-erased one: a typed term is opaque to a user who
-- imports only this layer, so a sort-erased instance would not apply to it without the bridges
-- below.

namespace TermToValue

instance [inst : TermToValue α] [ToTyp α] : Untyped.TermToValue α where
  termToValue t := t.typeCheckAs α >>= inst.termToValue

instance [inst : Untyped.TermToValue α] : TermToValue α where
  termToValue t := inst.termToValue t.erase

end TermToValue

-- no `TermToValue (Term α)`: `TermToValue β` reads a `Term β`, so at `β := Term α` it would have to
-- read a `Term (Term α)`. An index describes a sort, and a term is not one.

/-- Builds the constant term denoting a Lean `α`. -/
class ValueToTerm (α : Type) where
  /-- Builds the constant term denoting a value. -/
  valueToTerm : [Ω] → α → Env (Term α)

/-- A Lean type usable as a sort, in both directions. -/
class abbrev SrtLike (α : Type) := ToTyp α, TermToValue α, ValueToTerm α

/-- The sort-erased conversion an instance of this layer's class induces. -/
@[reducible]
def TermToValue.toUntyped [A : TermToValue α] : Untyped.TermToValue α := ⟨A.termToValue⟩
-- `reducible` so that instance resolution sees through it where a sort-erased conversion is what a
-- delegation needs.

@[inherit_doc TermToValue.toUntyped, reducible]
def ValueToTerm.toUntyped [A : ValueToTerm α] : Untyped.ValueToTerm α := ⟨A.valueToTerm⟩

/-- The typed conversion a sort-erased instance induces: the term is relaxed before it is read. -/
@[reducible]
def _root_.Cvc.Untyped.TermToValue.toTyped [A : Untyped.TermToValue α] : TermToValue α :=
  ⟨fun t => A.termToValue t.erase⟩

/-- The typed conversion a sort-erased instance induces: the term built is checked against `α`. -/
@[reducible]
def _root_.Cvc.Untyped.ValueToTerm.toTyped [ToTyp α] [A : Untyped.ValueToTerm α]
: ValueToTerm α :=
  ⟨fun v => A.valueToTerm v >>= (·.typeCheckAs α)⟩

namespace ValueToTerm

-- low priority both ways, so that an instance written for a layer wins over one bridged from the
-- other: the bridge from sort-erased checks the term it builds, which a direct instance need not
instance (priority := low) [ValueToTerm α] : Untyped.ValueToTerm α := ValueToTerm.toUntyped

instance (priority := low) [ToTyp α] [Untyped.ValueToTerm α] : ValueToTerm α :=
  Untyped.ValueToTerm.toTyped

end ValueToTerm

namespace Term

/-- The constant term denoting a value. -/
def mkValue [A : ValueToTerm α] : (value : α) → Env (Term α) := A.valueToTerm

@[inherit_doc mkValue]
def mkValueAs (α : Type) [ValueToTerm α] : (value : α) → Env (Term α) := mkValue

/-- The value a constant term denotes. -/
def extractValue [A : TermToValue α] : Term α → Env α := A.termToValue

@[inherit_doc extractValue]
def extractValueAs (α : Type) [TermToValue α] : Term α → Env α := extractValue



/-! ## Reading a term's own structure

These take a term at any index. Children come back sort-erased, since a term's index says nothing
about its children's.
-/

/-- The sort of a term, which is `Srt.of α`. -/
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
