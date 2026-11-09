/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs

public import Cvc.Untyped.Theory.BitVec
public import Cvc.Gen.TypedView
public import Cvc.Typed.Core.View
public import Cvc.Typed.Core.Value
public import Cvc.Spec.BitVec



/-! # Bit-vectors, typed

A result's width is computed from its arguments' and indices: `bvConcat` is
`Term (BitVec n) → Term (BitVec m) → Env (Term (BitVec (n + m)))`, matching `BitVec.append`.
-/
namespace Cvc.Typed.Term public section

open Cvc renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Spec.BitVec
gen_typed_view% from Cvc.Spec.BitVec



/-! ## Values -/

@[inherit_doc T.isBitVecValue]
def isBitVecValue (term : Term (BitVec size)) : Bool := T.isBitVecValue term


@[inherit_doc T.getBitVecValue]
def getBitVecValue (term : Term (BitVec size)) : Env (BitVec size) := T.getBitVecValue term

instance : SrtLike (BitVec size) where
  -- `mkBitVec` takes a `UInt64`, so a wider value goes through its binary digits
  valueToTerm bv :=
    if size ≤ 64 then mkBitVec size bv.toNat.toUInt64
    else mkBitVecOfString size (String.ofList (Nat.toDigits 2 bv.toNat)) 2
  termToValue := getBitVecValue
