/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Term.Defs

public import Cvc.Untyped.Term.Defs
public import Cvc.Ext
public import Cvc.Untyped.Term.Value
public import Cvc.Types.FiniteField
public import Cvc.Srt
public import Cvc.Gen
public import Cvc.Spec.FiniteField



/-! # Generated FiniteField constructors, sort-erased -/
namespace Cvc.Untyped.Term public section

open cvc5 renaming Term → T

variable [Ω]

gen_untyped% from Cvc.Spec.FiniteField


/-- An element of the finite field a sort describes.

Not generated: cvc5 takes the value *before* the sort, against the argument order every other
constructor uses.
-/
def mkFiniteFieldElem (value : Int) (srt : Srt) : Env Term :=
  runUnsafe fun tm => tm.mkFiniteFieldElem value srt.toUnsafe



/-! ## Values

The size lives in the sort, so reading a value back recovers it from there and checks it against
the one asked for.
-/

@[inherit_doc T.isFiniteFieldValue]
def isFiniteFieldValue (term : Term) : Bool := T.isFiniteFieldValue term.toUnsafe

/-- The integer representing a constant finite-field element, in cvc5's symmetric representation. -/
def getFiniteFieldRepr (term : Term) : Res Int :=
  T.getFiniteFieldValue term.toUnsafe |>.mapError Error.ofUnsafe


namespace FiniteField

/-- The term denoting an element of a finite field of known size. -/
def toTerm (elem : Cvc.FiniteField size) : Env Term := do
  mkFiniteFieldElem elem.repr (← Srt.of (Cvc.FiniteField size))

/-- The finite-field element a constant term denotes, at whatever size it turns out to have. -/
def ofTermErased (term : Term) : Env Cvc.FiniteField.Erased := do
  let size ← (← term.getSort).getFiniteFieldSize
  return {size, get := {repr := ← term.toUnsafe.getFiniteFieldValue}}

/-- The finite-field element a constant term denotes, failing unless the size is the expected. -/
def ofTerm (term : Term) : Env (Cvc.FiniteField size) := do
  let ⟨size', elem⟩ ← ofTermErased term
  if h : size' = size then return h ▸ elem
  else throwUser <|
    s!"expected a finite-field element of size {size}, got one of size {size'}: `{term}`"

end FiniteField

instance : SrtLike (Cvc.FiniteField size) where
  valueToTerm := FiniteField.toTerm
  termToValue := FiniteField.ofTerm
