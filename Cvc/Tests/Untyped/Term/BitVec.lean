/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Term.BitVec
import Cvc.Untyped.Term.Bool

public meta import Cvc.Untyped.Term.BitVec
public meta import Cvc.Untyped.Term.Bool



/-! # Generated bit-vector constructors, sort-erased -/
namespace Cvc.Tests.Untyped.Term.BitVec

open Cvc
open Cvc.Untyped.Term

/-- info:
bvNot    : (bvnot u)
bvAnd    : (bvand u v)
bvOr     : (bvor u v)
bvXor    : (bvxor u v)
bvNeg    : (bvneg u)
bvAdd    : (bvadd u v)
bvSub    : (bvsub u v)
bvMul    : (bvmul u v)
bvUdiv   : (bvudiv u v)
bvSrem   : (bvsrem u v)
bvShl    : (bvshl u v)
bvAshr   : (bvashr u v)
bvUlt    : (bvult u v)
bvSge    : (bvsge u v)
bvConcat : (concat u w)
bvComp   : (bvcomp u v)
bvRedor  : (bvredor u)
bvToNat  : (ubv_to_int u)
-/
#guard_msgs in #eval Env.runIO do
  let u ← Cvc.Untyped.Term.mkSymbolAs (BitVec 4) "u"
  let v ← Cvc.Untyped.Term.mkSymbolAs (BitVec 4) "v"
  let w ← Cvc.Untyped.Term.mkSymbolAs (BitVec 6) "w"

  println! "bvNot    : {← bvNot u}"
  println! "bvAnd    : {← bvAnd u v}"
  println! "bvOr     : {← bvOr u v}"
  println! "bvXor    : {← bvXor u v}"
  println! "bvNeg    : {← bvNeg u}"
  println! "bvAdd    : {← bvAdd u v}"
  println! "bvSub    : {← bvSub u v}"
  println! "bvMul    : {← bvMul u v}"
  println! "bvUdiv   : {← bvUdiv u v}"
  println! "bvSrem   : {← bvSrem u v}"
  println! "bvShl    : {← bvShl u v}"
  println! "bvAshr   : {← bvAshr u v}"
  println! "bvUlt    : {← bvUlt u v}"
  println! "bvSge    : {← bvSge u v}"
  println! "bvConcat : {← bvConcat u w}"
  println! "bvComp   : {← bvComp u v}"
  println! "bvRedor  : {← bvRedor u}"
  println! "bvToNat  : {← bvToNat u}"

/-! ## Overflow predicates and conversions -/

/-- info:
bvIte      : (bvite c u v)
bvUbvToInt : (ubv_to_int u)
bvSbvToInt : (sbv_to_int u)
bvNego     : (bvnego u)
bvUaddo    : (bvuaddo u v)
bvSaddo    : (bvsaddo u v)
bvUsubo    : (bvusubo u v)
bvSsubo    : (bvssubo u v)
bvUmulo    : (bvumulo u v)
bvSmulo    : (bvsmulo u v)
bvSdivo    : (bvsdivo u v)
bvUltbv    : (bvultbv u v)
bvSltbv    : (bvsltbv u v)
-/
#guard_msgs in #eval Env.runIO do
  let u ← Cvc.Untyped.Term.mkSymbolAs (BitVec 4) "u"
  let v ← Cvc.Untyped.Term.mkSymbolAs (BitVec 4) "v"
  let c ← Cvc.Untyped.Term.mkSymbolAs (BitVec 1) "c"

  println! "bvIte      : {← bvIte c u v}"
  println! "bvUbvToInt : {← bvUbvToInt u}"
  println! "bvSbvToInt : {← bvSbvToInt u}"
  println! "bvNego     : {← bvNego u}"
  println! "bvUaddo    : {← bvUaddo u v}"
  println! "bvSaddo    : {← bvSaddo u v}"
  println! "bvUsubo    : {← bvUsubo u v}"
  println! "bvSsubo    : {← bvSsubo u v}"
  println! "bvUmulo    : {← bvUmulo u v}"
  println! "bvSmulo    : {← bvSmulo u v}"
  println! "bvSdivo    : {← bvSdivo u v}"
  println! "bvUltbv    : {← bvUltbv u v}"
  println! "bvSltbv    : {← bvSltbv u v}"

/-! ## Indexed operators -/

/-- info:
extract    : ((_ extract 5 2) u)
repeat     : ((_ repeat 3) u)
zeroExtend : ((_ zero_extend 4) u)
signExtend : ((_ sign_extend 4) u)
rotateLeft : ((_ rotate_left 2) u)
rotateRight: ((_ rotate_right 2) u)
bit        : ((_ @bit 3) u)
intToBv    : ((_ int_to_bv 8) i)
-/
#guard_msgs in #eval Env.runIO do
  let u ← Cvc.Untyped.Term.mkSymbolAs (BitVec 8) "u"
  let i ← Cvc.Untyped.Term.mkSymbolAs (Int) "i"

  println! "extract    : {← bvExtract 5 2 u}"
  println! "repeat     : {← bvRepeat 3 u}"
  println! "zeroExtend : {← bvZeroExtend 4 u}"
  println! "signExtend : {← bvSignExtend 4 u}"
  println! "rotateLeft : {← bvRotateLeft 2 u}"
  println! "rotateRight: {← bvRotateRight 2 u}"
  println! "bit        : {← bvBit 3 u}"
  println! "intToBv    : {← intToBv 8 i}"

/-! ## Constructors -/

/-- info:
mkBitVec        : #b00000101
mkBitVecOfString: #b11111111
-/
#guard_msgs in #eval Env.runIO do
  println! "mkBitVec        : {← mkBitVec 8 5}"
  println! "mkBitVecOfString: {← mkBitVecOfString 8 "ff" 16}"

/-! ## From booleans

The result's size is the operator's own arity, not a function of its arguments' sorts.
-/

/-- info:
one bit : (@from_bools a)
two     : (@from_bools a b)
three   : (@from_bools a b c)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Untyped.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Untyped.Term.mkSymbolAs Bool "b"
  let c ← Cvc.Untyped.Term.mkSymbolAs Bool "c"

  println! "one bit : {← bvFromBool a}"
  println! "two     : {← bvFromBools #[a, b]}"
  println! "three   : {← bvFromBools #[a, b, c]}"
