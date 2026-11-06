/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.BitVec
import Cvc.Typed.Core.Bool

public meta import Cvc.Typed.Theory.BitVec
public meta import Cvc.Typed.Core.Bool



/-! # Generated bit-vector constructors, typed -/
namespace Cvc.Tests.Typed.Term.BitVec

open Cvc
open Cvc.Typed (Term)
open Cvc.Typed.Term

/-- info:
bvNot    : (bvnot u)
bvAnd    : (bvand u v)
bvAdd    : (bvadd u v)
bvMul    : (bvmul u v)
bvShl    : (bvshl u v)
bvUlt    : (bvult u v)
bvSle    : (bvsle u v)
bvConcat : (concat u w)
bvComp   : (bvcomp u v)
ubvToInt : (ubv_to_int u)
-/
#guard_msgs in #eval Env.runIO do
  let u ← Cvc.Typed.Term.mkSymbolAs (BitVec 4) "u"
  let v ← Cvc.Typed.Term.mkSymbolAs (BitVec 4) "v"
  let w ← Cvc.Typed.Term.mkSymbolAs (BitVec 6) "w"

  println! "bvNot    : {← bvNot u}"
  println! "bvAnd    : {← bvAnd u v}"
  println! "bvAdd    : {← bvAdd u v}"
  println! "bvMul    : {← bvMul u v}"
  println! "bvShl    : {← bvShl u v}"
  println! "bvUlt    : {← bvUlt u v}"
  println! "bvSle    : {← bvSle u v}"
  println! "bvConcat : {← bvConcat u w}"
  println! "bvComp   : {← bvComp u v}"
  println! "ubvToInt : {← bvUbvToInt u}"

section sizes
variable [Ω] (u v : Term (BitVec 4)) (w : Term (BitVec 6))

/-- Size-preserving operators keep their argument's size. -/
example : Env (Term (BitVec 4)) := bvAdd u v
/-- Concatenation adds sizes, definitionally. -/
example : Env (Term (BitVec 10)) := bvConcat u w
/-- Concatenation is associative on sizes too. -/
example : Env (Term (BitVec 14)) := do bvConcat (← bvConcat u w) u
/-- Comparisons drop to `Bool`. -/
example : Env (Term Bool) := bvUlt u v
/-- Reductions land at size one. -/
example : Env (Term (BitVec 1)) := bvComp u v
/-- Conversion to integers. -/
example : Env (Term Int) := bvUbvToInt u

end sizes

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
  let u ← Cvc.Typed.Term.mkSymbolAs (BitVec 4) "u"
  let v ← Cvc.Typed.Term.mkSymbolAs (BitVec 4) "v"
  let c ← Cvc.Typed.Term.mkSymbolAs (BitVec 1) "c"

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
  let u ← Cvc.Typed.Term.mkSymbolAs (BitVec 8) "u"
  let i ← Cvc.Typed.Term.mkSymbolAs (Int) "i"

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
they exist exactly where the theory does. What the typed layer adds is the *index* the expansion
carries, pinned by the `example`s below.
-/

open Cvc.Typed in
/-- info:
bv and      : (bvand u v)
bv or       : (bvor u v)
bv xor      : (bvxor u v)
bv shl      : (bvshl u v)
bv lshr     : (bvlshr u v)
||| under &&&: (bvor u (bvand v u))
-/
#guard_msgs in #eval Env.runIO do
  let u ← mkSymbolAs (BitVec 4) "u"
  let v ← mkSymbolAs (BitVec 4) "v"

  println! "bv and      : {← smt! u &&& v}"
  println! "bv or       : {← smt! u ||| v}"
  println! "bv xor      : {← smt! u ^^^ v}"
  println! "bv shl      : {← smt! u <<< v}"
  println! "bv lshr     : {← smt! u >>> v}"
  println! "||| under &&&: {← smt! u ||| v &&& u}"

section indices
open Cvc.Typed
variable [Ω] (u v : Term (BitVec 4))

/-- The bit-vector notations keep the width. -/
example : Env (Term (BitVec 4)) := smt! u &&& v <<< u
/-- Escaping keeps whatever index the Lean term has. -/
example : Env (Term (BitVec 4)) := smt! ![Cvc.Typed.Term.bvAdd u v]

end indices

/-! A value wider than 64 bits keeps every bit on its way to a term. -/

/-- info: 2^70 + 5 at width 72 : 0x400000000000000005#72 -/
#guard_msgs in #eval Env.runIO do
  let t ← Cvc.Typed.Term.mkValue (BitVec.ofNat 72 (2^70 + 5))
  println! "2^70 + 5 at width 72 : {← Cvc.Typed.Term.getBitVecValue (size := 72) t}"
