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

public import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Types.Set
public import Cvc.Gen.Term
public import Cvc.Spec.Set



/-! # Generated Set constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.Set



/-! ## Values

A `Cvc.Set` denotes an SMT set: the empty set, with each element inserted.
-/

@[inherit_doc T.isSetValue]
def isSetValue (term : Term) : Bool := T.isSetValue term.toUnsafe


/-- The elements a constant set term denotes. -/
def getSetElems (term : Term) : Env Terms := do
  let elems : Terms ← T.getSetValue term.toUnsafe |>.mapError Error.ofUnsafe
  return elems

section variable [Ord α] [ToTyp α]

/-- The set term denoting a set of values. -/
def mkSetValue [ValueToTerm α] (set : Cvc.Set α) : Env Term := do
  let mut term ← Srt.of α >>= setEmpty
  for elem in set do
    term ← mkValue elem >>= (setInsert · term)
  return term

/-- The set of values a constant set term denotes. -/
def getSetValue [TermToValue α] (term : Term) : Env (Cvc.Set α) := do
  let elems ← term.getSetElems
  elems.foldlM (init := Cvc.Set.empty) fun set elem => set.insert <$> extractValue elem

instance [ValueToTerm α] : ValueToTerm (Cvc.Set α) := ⟨mkSetValue⟩
instance [TermToValue α] : TermToValue (Cvc.Set α) := ⟨getSetValue⟩

end
