/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

public import Cvc.Untyped.Core.Defs
public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.Core.Bool



/-! # Nullable constructors, sort-erased

cvc5's `Nullable` is the `Option` sort: a value is either `nullable.null` or `nullable.some v`.
Unlike a declared datatype, `Srt.nullable` gives the same sort every time for the same element sort.

It is a datatype underneath, so a nullable value is an `APPLY_CONSTRUCTOR` term.
-/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T



/-! ## Constructors -/

/-- The null value of the nullable sort over the element sort `elm`. -/
def mkNull (elm : Srt) : Env Term := do
  let srt ← Srt.nullable elm
  runUnsafe fun tm => tm.mkNullableNull srt
-- Takes the *element* sort, as every constructor of a polymorphic sort does; cvc5's own method
-- wants the nullable sort, which is built here.

/-- The nullable value holding `elem`, `nullable.some elem`. -/
def nullableSome (elem : Term) : Env Term :=
  runUnsafe fun tm => tm.mkNullableSome elem

/-- The element the nullable term `nullable` holds, `nullable.val`. -/
def nullableVal (nullable : Term) : Env Term :=
  runUnsafe fun tm => tm.mkNullableVal nullable

/-- Whether the nullable term `nullable` is null, `nullable.is_null`. -/
def nullableIsNull (nullable : Term) : Env Term :=
  runUnsafe fun tm => tm.mkNullableIsNull nullable

/-- Whether the nullable term `nullable` holds an element, `nullable.is_some`. -/
def nullableIsSome (nullable : Term) : Env Term :=
  runUnsafe fun tm => tm.mkNullableIsSome nullable



/-! ## Values

A nullable value is the constructor applied to nothing or to one element, so it is read off the
term's kind and children. Unlike a set or a sequence, this works on a built term as well as on a
model's answer.
-/

/-- The element a nullable term denotes, or `none` if it denotes the null value.

Fails unless the term is built by a nullable constructor (see `isNullableValue`): a declared
constant of nullable sort, for instance, is not.
-/
def getNullableElem? (term : Term) : Env (Option Term) := do
  let some .APPLY_CONSTRUCTOR := term.getKind?
    | throwUser s!"expected a nullable value, got `{term}`"
  let kids := term.getKids
  let some ctor := kids[0]?
    | throwInternal s!"nullable value `{term}` has no constructor"
  match ← ctor.getSymbol with
  | "nullable.null" => return none
  | "nullable.some" =>
    let some elem := kids[1]?
      | throwInternal s!"`nullable.some` applied to nothing in `{term}`"
    return some elem
  | symbol => throwUser s!"expected a nullable value, got constructor `{symbol}`"

/-- Whether a term is built by a nullable constructor, `nullable.null` or `nullable.some`.

That is what `getNullableElem?` needs. Being nullable-sorted is not enough: a declared constant of
nullable sort is built by neither.
-/
def isNullableValue (term : Term) : Env Bool := do
  return (← term.getSort).isNullable && term.getKind? matches some .APPLY_CONSTRUCTOR


section variable [ToTyp α]

/-- The nullable term denoting an optional value. -/
def mkNullableValue [ValueToTerm α] (value : Option α) : Env Term :=
  match value with
  | none => Srt.of α >>= mkNull
  | some elem => mkValue elem >>= nullableSome

/-- The optional value a nullable term denotes. -/
def getNullableValue [TermToValue α] (term : Term) : Env (Option α) := do
  match ← term.getNullableElem? with
  | none => return none
  | some elem => some <$> extractValue elem

instance [ValueToTerm α] : ValueToTerm (Option α) := ⟨mkNullableValue⟩
instance [TermToValue α] : TermToValue (Option α) := ⟨getNullableValue⟩

end
