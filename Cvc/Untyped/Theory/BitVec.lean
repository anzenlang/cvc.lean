/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs

public import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Gen
public import Cvc.Spec.BitVec



/-! # Generated bit-vector constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.BitVec



/-! ## Values -/

@[inherit_doc T.isBitVectorValue]
def isBitVecValue (term : Term) : Bool := T.isBitVectorValue term.toUnsafe


/-- The bit-vector a constant term denotes, failing unless it has the expected size.

cvc5 reports the value as its base-2 representation, so the size comes out of the string's length
and has to be checked against the one asked for.
-/
def getBitVecValue (term : Term) : Env (BitVec size) := do
  let binRepr ← T.getBitVectorValue term.toUnsafe 2 |>.mapError Error.ofUnsafe
  let empty : (size : Nat) × BitVec size := ⟨0, BitVec.zero 0⟩
  let ⟨size', bv⟩ ← binRepr.chars.foldM (init := empty) fun
    | ⟨size, bv⟩, '0' => pure ⟨size + 1, bv.concat false⟩
    | ⟨size, bv⟩, '1' => pure ⟨size + 1, bv.concat true⟩
    | _, c => throwInternal
      s!"unexpected character `{c}` in binary representation `{binRepr}` for bitvec term `{term}`"
  if h : size' = size
  then return h ▸ bv
  else throwUser s!"expected bitvector term of size {size}, got size {size'}: {term}"

instance : SrtLike (BitVec size) where
  valueToTerm bv := mkBitVec size bv.toNat.toUInt64
  termToValue t := t.getBitVecValue
