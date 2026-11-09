/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Bit-vector specification

The overflow predicates produce `Bool`, while `bvUltbv`/`bvSltbv` produce a one-bit bit-vector.
-/
namespace Cvc public section



/-! ## Bitwise, arithmetic, shifts and comparison -/

/-- Bitwise negation. -/
op% bvNot {n : size} (bv : bitVec n) : bitVec n := BITVECTOR_NOT

/-- Bitwise conjunction. -/
op% bvAnd {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_AND infixl "&&&" 60

/-- Bitwise disjunction. -/
op% bvOr {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_OR infixl "|||" 55

/-- Bitwise exclusive disjunction. -/
op% bvXor {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_XOR infixl "^^^" 58

/-- Bitwise negated conjunction. -/
op% bvNand {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_NAND

/-- Bitwise negated disjunction. -/
op% bvNor {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_NOR

/-- Bitwise negated exclusive disjunction. -/
op% bvXnor {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_XNOR

/-- Two's-complement negation. -/
op% bvNeg {n : size} (bv : bitVec n) : bitVec n := BITVECTOR_NEG

/-- Addition modulo `2 ^ n`. -/
op% bvAdd {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_ADD

/-- Subtraction modulo `2 ^ n`. -/
op% bvSub {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_SUB

/-- Multiplication modulo `2 ^ n`. -/
op% bvMul {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_MULT

/-- Unsigned division, truncating towards zero; all ones on a zero divisor. -/
op% bvUdiv {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_UDIV

/-- Unsigned remainder; the dividend on a zero divisor. -/
op% bvUrem {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_UREM

/-- Signed division, truncating towards zero.

On a zero divisor: `-1` for a non-negative dividend, `1` for a negative one.
-/
op% bvSdiv {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_SDIV

/-- Signed remainder, sign following the dividend; the dividend on a zero divisor. -/
op% bvSrem {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_SREM

/-- Signed remainder, sign following the divisor; the dividend on a zero divisor. -/
op% bvSmod {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_SMOD

/-- Logical left shift of `lft` by `rgt` bits. -/
op% bvShl {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_SHL infixl "<<<" 75

/-- Logical right shift of `lft` by `rgt` bits. -/
op% bvLshr {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_LSHR infixl ">>>" 75

/-- Arithmetic right shift of `lft` by `rgt` bits. -/
op% bvAshr {n : size} (lft rgt : bitVec n) : bitVec n := BITVECTOR_ASHR

/-- Unsigned less-than. -/
op% bvUlt {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_ULT

/-- Unsigned less-than-or-equal-to. -/
op% bvUle {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_ULE

/-- Unsigned greater-than. -/
op% bvUgt {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_UGT

/-- Unsigned greater-than-or-equal-to. -/
op% bvUge {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_UGE

/-- Signed less-than. -/
op% bvSlt {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SLT

/-- Signed less-than-or-equal-to. -/
op% bvSle {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SLE

/-- Signed greater-than. -/
op% bvSgt {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SGT

/-- Signed greater-than-or-equal-to. -/
op% bvSge {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SGE

/-- Concatenation, `lft` giving the most significant bits. -/
op% bvConcat {n m : size} (lft : bitVec n) (rgt : bitVec m) : bitVec (n + m)
  := BITVECTOR_CONCAT

/-- Bit-level comparison, `1` when both arguments are equal and `0` otherwise. -/
op% bvComp {n : size} (lft rgt : bitVec n) : bitVec 1 := BITVECTOR_COMP

/-- Conjunction of all the bits, as a one-bit bit-vector. -/
op% bvRedand {n : size} (bv : bitVec n) : bitVec 1 := BITVECTOR_REDAND

/-- Disjunction of all the bits, as a one-bit bit-vector. -/
op% bvRedor {n : size} (bv : bitVec n) : bitVec 1 := BITVECTOR_REDOR



/-! ## Overflow predicates and conversions -/

/-- Bit-vector conditional, selecting on a one-bit condition. -/
op% bvIte {n : size} (cnd : bitVec 1) (thn els : bitVec n) : bitVec n := BITVECTOR_ITE

/-- Conversion to an integer, reading the bit-vector as unsigned. -/
op% bvUbvToInt {n : size} (bv : bitVec n) : int := BITVECTOR_UBV_TO_INT

/-- Conversion to an integer, reading the bit-vector as signed. -/
op% bvSbvToInt {n : size} (bv : bitVec n) : int := BITVECTOR_SBV_TO_INT

/-- Whether two's-complement negation overflows. -/
op% bvNego {n : size} (bv : bitVec n) : bool := BITVECTOR_NEGO

/-- Whether unsigned addition overflows. -/
op% bvUaddo {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_UADDO

/-- Whether signed addition overflows. -/
op% bvSaddo {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SADDO

/-- Whether unsigned subtraction overflows. -/
op% bvUsubo {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_USUBO

/-- Whether signed subtraction overflows. -/
op% bvSsubo {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SSUBO

/-- Whether unsigned multiplication overflows. -/
op% bvUmulo {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_UMULO

/-- Whether signed multiplication overflows. -/
op% bvSmulo {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SMULO

/-- Whether signed division overflows. -/
op% bvSdivo {n : size} (lft rgt : bitVec n) : bool := BITVECTOR_SDIVO

/-- Unsigned less-than, as a one-bit bit-vector. -/
op% bvUltbv {n : size} (lft rgt : bitVec n) : bitVec 1 := BITVECTOR_ULTBV

/-- Signed less-than, as a one-bit bit-vector. -/
op% bvSltbv {n : size} (lft rgt : bitVec n) : bitVec 1 := BITVECTOR_SLTBV



/-! ## Indexed operators -/

/-- Bits `hi` down to `lo` of `bv`, bit 0 being the least significant; needs `lo ≤ hi < n`. -/
op% bvExtract [hi lo] {n : size} (bv : bitVec n) : bitVec (hi - lo + 1) := BITVECTOR_EXTRACT

/-- The given number of copies of a bit-vector, concatenated. -/
op% bvRepeat [count] {n : size} (bv : bitVec n) : bitVec (n * count) := BITVECTOR_REPEAT

/-- Extension with the given number of zeroes. -/
op% bvZeroExtend [extra] {n : size} (bv : bitVec n) : bitVec (n + extra) := BITVECTOR_ZERO_EXTEND

/-- Extension with the given number of copies of the sign bit. -/
op% bvSignExtend [extra] {n : size} (bv : bitVec n) : bitVec (n + extra) := BITVECTOR_SIGN_EXTEND

/-- Rotation to the left by the given number of bits. -/
op% bvRotateLeft [count] {n : size} (bv : bitVec n) : bitVec n := BITVECTOR_ROTATE_LEFT

/-- Rotation to the right by the given number of bits. -/
op% bvRotateRight [count] {n : size} (bv : bitVec n) : bitVec n := BITVECTOR_ROTATE_RIGHT

/-- Conversion of an integer to a bit-vector of the given size, modulo `2 ^ size`. -/
op% intToBv [size] (arg : int) : bitVec size := INT_TO_BITVECTOR

/-! ## Constructors

The size is an index, so it is an explicit `Nat` and also fixes the result's own size.
-/

/-- A bit-vector literal of the given size, keeping the low `size` bits of `value`. -/
op% mkBitVec [size] (value :! UInt64) : bitVec size := CONST_BITVECTOR tm mkBitVector

/-- A bit-vector literal of the given size, read in `base`, which must be 2, 10 or 16. -/
op% mkBitVecOfString [size] (repr :! String) (base :! UInt32) : bitVec size
  := CONST_BITVECTOR tm mkBitVectorOfString
