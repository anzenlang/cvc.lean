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
import all Cvc.Typed.Core.Defs

public import Cvc.Untyped.Theory.Nullable
public import Cvc.Typed.Core.Defs
public import Cvc.Typed.Core.Value
public import Cvc.Typed.Core.Bool



/-! # Nullable constructors, typed

cvc5's `Nullable` is denoted by Lean's `Option`, so a nullable term is a `Term (Option α)` and the
element it carries is a `Term α`. The index is what tells `mkNull` which sort to build, where the
sort-erased version takes the element sort.
-/
namespace Cvc.Typed.Term public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## Constructors -/

/-- The null value at `Option α`. -/
def mkNull' (α : Type) [ToTyp α] : Env (Term (Option α)) := do
  T.mkNull (← Srt.of α)

@[inherit_doc mkNull']
abbrev mkNull [ToTyp α] : Env (Term (Option α)) := mkNull' α

@[inherit_doc T.nullableSome]
def nullableSome : Term α → Env (Term (Option α)) := T.nullableSome

@[inherit_doc T.nullableVal]
def nullableVal : Term (Option α) → Env (Term α) := T.nullableVal

@[inherit_doc T.nullableIsNull]
def nullableIsNull : Term (Option α) → Env (Term Bool) := T.nullableIsNull

@[inherit_doc T.nullableIsSome]
def nullableIsSome : Term (Option α) → Env (Term Bool) := T.nullableIsSome



/-! ## Values -/

@[inherit_doc T.isNullableValue]
def isNullableValue : Term (Option α) → Env Bool := T.isNullableValue

/-- The element a nullable term denotes, or `none` if it denotes the null value. -/
def getNullableElem? : Term (Option α) → Env (Option (Term α)) := T.getNullableElem?


section variable [ToTyp α]

/-- The nullable term denoting an optional value. -/
def mkNullableValue [ValueToTerm α] : (value : Option α) → Env (Term (Option α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkNullableValue

/-- The optional value a nullable term denotes. -/
def getNullableValue [TermToValue α] : Term (Option α) → Env (Option α) :=
  have := TermToValue.toUntyped (α := α)
  T.getNullableValue

instance [ValueToTerm α] : ValueToTerm (Option α) := ⟨mkNullableValue⟩
instance [TermToValue α] : TermToValue (Option α) := ⟨getNullableValue⟩

end
