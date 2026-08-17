/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Floating-point specification

The operators taking a rounding mode take it first, as cvc5 does. The predicates and the
conversions that read a bit pattern take none.
-/
namespace Cvc public section



/-! ## Predicates -/

/-- Floating-point equality, for which `NaN` is not equal to itself and the zeroes are equal. -/
op% fpEq {e s : size} (lft rgt : float e s) : bool := FLOATINGPOINT_EQ

/-- Less-than. -/
op% fpLt {e s : size} (lft rgt : float e s) : bool := FLOATINGPOINT_LT

/-- Less-than-or-equal-to. -/
op% fpLe {e s : size} (lft rgt : float e s) : bool := FLOATINGPOINT_LEQ

/-- Greater-than. -/
op% fpGt {e s : size} (lft rgt : float e s) : bool := FLOATINGPOINT_GT

/-- Greater-than-or-equal-to. -/
op% fpGe {e s : size} (lft rgt : float e s) : bool := FLOATINGPOINT_GEQ

/-- Whether the value is normal. -/
op% fpIsNormal {e s : size} (fp : float e s) : bool := FLOATINGPOINT_IS_NORMAL

/-- Whether the value is subnormal. -/
op% fpIsSubnormal {e s : size} (fp : float e s) : bool := FLOATINGPOINT_IS_SUBNORMAL

/-- Whether the value is either zero. -/
op% fpIsZero {e s : size} (fp : float e s) : bool := FLOATINGPOINT_IS_ZERO

/-- Whether the value is either infinity. -/
op% fpIsInf {e s : size} (fp : float e s) : bool := FLOATINGPOINT_IS_INF

/-- Whether the value is not-a-number. -/
op% fpIsNan {e s : size} (fp : float e s) : bool := FLOATINGPOINT_IS_NAN

/-- Whether the value is negative. -/
op% fpIsNeg {e s : size} (fp : float e s) : bool := FLOATINGPOINT_IS_NEG

/-- Whether the value is positive. -/
op% fpIsPos {e s : size} (fp : float e s) : bool := FLOATINGPOINT_IS_POS



/-! ## Arithmetic and assembly -/

/-- Absolute value. -/
op% fpAbs {e s : size} (fp : float e s) : float e s := FLOATINGPOINT_ABS

/-- Negation. -/
op% fpNeg {e s : size} (fp : float e s) : float e s := FLOATINGPOINT_NEG

/-- Addition. -/
op% fpAdd {e s : size} (rm : roundingMode) (lft rgt : float e s) : float e s := FLOATINGPOINT_ADD

/-- Subtraction. -/
op% fpSub {e s : size} (rm : roundingMode) (lft rgt : float e s) : float e s := FLOATINGPOINT_SUB

/-- Multiplication. -/
op% fpMul {e s : size} (rm : roundingMode) (lft rgt : float e s) : float e s := FLOATINGPOINT_MULT

/-- Division. -/
op% fpDiv {e s : size} (rm : roundingMode) (lft rgt : float e s) : float e s := FLOATINGPOINT_DIV

/-- Fused multiply-add, computing `a * b + c` with a single rounding. -/
op% fpFma {e s : size} (rm : roundingMode) (a b c : float e s) : float e s := FLOATINGPOINT_FMA

/-- Square root. -/
op% fpSqrt {e s : size} (rm : roundingMode) (fp : float e s) : float e s := FLOATINGPOINT_SQRT

/-- Rounding to an integral value. -/
op% fpRti {e s : size} (rm : roundingMode) (fp : float e s) : float e s := FLOATINGPOINT_RTI

/-- Remainder. -/
op% fpRem {e s : size} (lft rgt : float e s) : float e s := FLOATINGPOINT_REM

/-- Minimum. -/
op% fpMin {e s : size} (lft rgt : float e s) : float e s := FLOATINGPOINT_MIN

/-- Maximum. -/
op% fpMax {e s : size} (lft rgt : float e s) : float e s := FLOATINGPOINT_MAX

/-- Conversion to a real. -/
op% fpToReal {e s : size} (fp : float e s) : real := FLOATINGPOINT_TO_REAL

/-- A floating point assembled from its sign, exponent and significand bits.

The significand bit-vector holds the significand *minus its hidden bit*, hence the `s + 1`.
-/
op% fpOfBits {e s : size} (sign : bitVec 1) (exponent : bitVec e) (significand : bitVec s)
  : float e (s + 1) := FLOATINGPOINT_FP



/-! ## Indexed conversions -/

/-- Reinterpretation of an IEEE-754 bit-vector as a floating point. -/
op% fpOfIeeeBv [e s] {n : size} (bv : bitVec n) : float e s
  := FLOATINGPOINT_TO_FP_FROM_IEEE_BV

/-- Conversion between floating-point formats. -/
op% fpOfFp [e s] {ei si : size} (rm : roundingMode) (fp : float ei si) : float e s
  := FLOATINGPOINT_TO_FP_FROM_FP

/-- Conversion of a real to a floating point. -/
op% fpOfReal [e s] (rm : roundingMode) (arg : real) : float e s
  := FLOATINGPOINT_TO_FP_FROM_REAL

/-- Conversion of a signed bit-vector to a floating point. -/
op% fpOfSbv [e s] {n : size} (rm : roundingMode) (bv : bitVec n) : float e s
  := FLOATINGPOINT_TO_FP_FROM_SBV

/-- Conversion of an unsigned bit-vector to a floating point. -/
op% fpOfUbv [e s] {n : size} (rm : roundingMode) (bv : bitVec n) : float e s
  := FLOATINGPOINT_TO_FP_FROM_UBV

/-- Conversion of a floating point to a signed bit-vector of the given size. -/
op% fpToSbv [size] {e s : size} (rm : roundingMode) (fp : float e s) : bitVec size
  := FLOATINGPOINT_TO_SBV

/-- Conversion of a floating point to an unsigned bit-vector of the given size. -/
op% fpToUbv [size] {e s : size} (rm : roundingMode) (fp : float e s) : bitVec size
  := FLOATINGPOINT_TO_UBV

/-! ## Constructors

The exponent and significand sizes are indices, so they are explicit `Nat`s and fix the result's
own sizes.
-/

/-- Not-a-number. -/
op% mkFloatNaN [exp sig] : float exp sig := CONST_FLOATINGPOINT tm mkFloatingPointNaN

/-- Positive infinity. -/
op% mkFloatPosInf [exp sig] : float exp sig := CONST_FLOATINGPOINT tm mkFloatingPointPosInf

/-- Negative infinity. -/
op% mkFloatNegInf [exp sig] : float exp sig := CONST_FLOATINGPOINT tm mkFloatingPointNegInf

/-- Positive zero. -/
op% mkFloatPosZero [exp sig] : float exp sig := CONST_FLOATINGPOINT tm mkFloatingPointPosZero

/-- Negative zero. -/
op% mkFloatNegZero [exp sig] : float exp sig := CONST_FLOATINGPOINT tm mkFloatingPointNegZero

/-- A floating point read from the bit pattern of a bit-vector. -/
op% mkFloat [exp sig] {n : size} (bv : bitVec n) : float exp sig
  := CONST_FLOATINGPOINT tm mkFloatingPoint
