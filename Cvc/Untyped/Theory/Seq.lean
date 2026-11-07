/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt
public import Cvc.Gen.View
public import Cvc.Untyped.Core.View

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

public import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Gen.Term
public import Cvc.Spec.Seq



/-! # Generated Seq constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.Seq
gen_untyped_view% from Cvc.Spec.Seq



/-! ## Values

A Lean `Array` denotes an SMT sequence: the empty sequence, then one unit sequence per element,
concatenated.
-/

/-- Whether a term is a sequence value, of kind `CONST_SEQUENCE`.

Such values are what a model answers; a sequence built from constructors, such as
`seqConcat (seqUnit 0) (seqUnit 1)`, is not one even when its elements are values.
-/
def isSeqValue (term : Term) : Bool := T.isSequenceValue term.toUnsafe


/-- The elements a constant sequence term denotes. -/
def getSeqValue [TermToValue α] (term : Term) : Env (Array α) := do
  let elems : Terms ← T.getSequenceValue term.toUnsafe |>.mapError Error.ofUnsafe
  elems.mapM extractValue

@[inherit_doc getSeqValue]
def getSeqValueOf (α : Type) [TermToValue α] : (term : Term) → Env (Array α) := getSeqValue

/-- The sequence term denoting an array of values. -/
def mkSeqValue [ToTyp α] [ValueToTerm α] (elems : Array α) : Env Term := do
  let units ← elems.mapM fun elem => do mkValue elem >>= seqUnit
  if let some fst := units[0]? then
    (units.drop 1).foldlM (init := fst) seqConcat
  else Srt.of α >>= mkEmptySeq
-- `mkEmptySeq` takes the *element* sort rather than the sequence's own, and an empty sequence
-- cannot be concatenated onto, so the empty case is separate rather than the fold's initial value.

instance [ToTyp α] [ValueToTerm α] : ValueToTerm (Array α) := ⟨mkSeqValue⟩
instance [TermToValue α] : TermToValue (Array α) := ⟨getSeqValue⟩
