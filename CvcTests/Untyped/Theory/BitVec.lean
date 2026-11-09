/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.BitVec
import Cvc.Untyped.Core.Bool

public meta import Cvc.Untyped.Theory.BitVec
public meta import Cvc.Untyped.Core.Bool



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
ubvToInt : (ubv_to_int u)
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
  println! "ubvToInt : {← bvUbvToInt u}"

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
  println! "intToBv    : {← intToBv 8 i}"

/-! ## Constructors -/

/-- info:
mkBitVec        : #b00000101
mkBitVecOfString: #b11111111
-/
#guard_msgs in #eval Env.runIO do
  println! "mkBitVec        : {← mkBitVec 8 5}"
  println! "mkBitVecOfString: {← mkBitVecOfString 8 "ff" 16}"

/-! # The `smt!` DSL, bit-vector notation

These notations come from this theory's `op%` entries and are emitted beside its constructors, so
they exist exactly where the theory does — importing another theory alone leaves them out of the
grammar. Their tests belong here for the same reason.
-/

open Cvc.Untyped in
/-- info:
bv and      : (bvand u v)
bv or       : (bvor u v)
bv xor      : (bvxor u v)
bv shl      : (bvshl u v)
bv lshr     : (bvlshr u v)
||| under &&&: (bvor u (bvand v u))
&&& under <<<: (bvand u (bvshl v u))
-/
#guard_msgs in #eval Env.runIO do
  let u ← mkSymbolAs (BitVec 4) "u"
  let v ← mkSymbolAs (BitVec 4) "v"

  -- the five carry the symbols Lean gives the same operations, at Lean's own precedences
  println! "bv and      : {← smt! u &&& v}"
  println! "bv or       : {← smt! u ||| v}"
  println! "bv xor      : {← smt! u ^^^ v}"
  println! "bv shl      : {← smt! u <<< v}"
  println! "bv lshr     : {← smt! u >>> v}"
  println! "||| under &&&: {← smt! u ||| v &&& u}"
  println! "&&& under <<<: {← smt! u &&& v <<< u}"

/-! A value wider than 64 bits keeps every bit on its way to a term. -/

/-- info: 2^70 + 5 at width 72 : 0x400000000000000005#72 -/
#guard_msgs in #eval Env.runIO do
  let t ← Cvc.Untyped.Term.mkValue (BitVec.ofNat 72 (2^70 + 5))
  println! "2^70 + 5 at width 72 : {← Cvc.Untyped.Term.getBitVecValue (size := 72) t}"
