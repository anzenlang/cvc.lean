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
-- `mkBool`/`mkInt` back the unit elements of the `N'` variants

public import Cvc.Ext
public import Cvc.Gen
public import Cvc.Untyped.Core.Value
public import Cvc.Spec.Bool



/-! # Generated Boolean and sort-generic constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.Bool

/-- A symbol of the sort `α` describes.

`mkSymbol` takes the sort itself; this names it by the Lean type denoting it.
-/
def mkSymbolAs (α : Type) [ToTyp α] (name : String) : Env Term := do
  mkSymbol (← Srt.of α) name



/-! ## Values -/

@[inherit_doc T.isBooleanValue]
def isBoolValue (term : Term) : Bool := T.isBooleanValue term.toUnsafe
/-- The boolean a term denotes, failing if it denotes none. -/
def getBoolValue (term : Term) : Res Bool :=
  T.getBooleanValue term.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getBoolValue]
def getBoolValue? (term : Term) : Option Bool := T.getBooleanValue? term.toUnsafe

instance : SrtLike Bool where
  valueToTerm := mkBool
  termToValue t := t.getBoolValue
