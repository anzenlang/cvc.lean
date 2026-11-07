/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Arithmetic specification

Integer and real arithmetic, the comparisons, the transcendental functions, and the predicates
over them.

Division and modulus come in two flavours: the plain ones leave the result on a zero divisor
unspecified, the `Total` ones define it — zero for a division, the dividend for `intModTotal` —
and are experimental in cvc5.
Integer division and modulus are Euclidean, as Lean's own `/` and `%` on `Int` are.
-/
namespace Cvc public section

/-! ## Constructors -/

/-- An integer literal. -/
op% mkInt (i :! Int) : int := CONST_INTEGER tm mkInteger

/-- An integer literal, read from its decimal representation. -/
op% mkIntOfString (repr :! String) : int := CONST_INTEGER tm mkIntegerOfString

/-- A real literal. -/
op% mkReal (r :! Rat) : real := CONST_RATIONAL tm mkRealOfRat

/-- A real literal, read from a decimal (`"1.5"`) or a fraction (`"3/4"`). -/
op% mkRealOfString (repr :! String) : real := CONST_RATIONAL tm mkRealOfString



/-! ## Arithmetic -/

/-- Arithmetic negation. -/
op% neg {α : IsArith} (arithTerm : α) : α := NEG prefix "-" 75 75

/-- Binary addition. -/
op% add {α : IsArith} (lft rgt : α) : α := ADD infixl "+" 65 unit 0

/-- Binary subtraction; `subN` is left-associative. -/
op% sub {α : IsArith} (lft rgt : α) : α := SUB infixl "-" 65 nary

/-- Binary multiplication. -/
op% mul {α : IsArith} (lft rgt : α) : α := MULT infixl "*" 70 unit 1

/-- Absolute value. -/
op% abs {α : IsArith} (arithTerm : α) : α := ABS

/-- Binary less-than; `ltN` chains: `ltN #[a, b, c]` is `a < b ∧ b < c`. -/
op% lt {α : IsArith} (lft rgt : α) : bool := LT infixr "<" 50 nary

/-- Binary less-than-or-equal-to; `leN` chains, as `ltN` does. -/
op% le {α : IsArith} (lft rgt : α) : bool := LEQ infixr "≤" 50 nary

/-- Binary greater-than; `gtN` chains, as `ltN` does. -/
op% gt {α : IsArith} (lft rgt : α) : bool := GT infixr ">" 50 nary

/-- Binary greater-than-or-equal-to; `geN` chains, as `ltN` does. -/
op% ge {α : IsArith} (lft rgt : α) : bool := GEQ infixr "≥" 50 nary



/-! ## Predicates -/

/-- Whether an arithmetic term denotes an integer. -/
op% isInt {α : IsArith} (arithTerm : α) : bool := IS_INTEGER



/-! ## Division, powers and conversions -/

/-- Real division, left-associative; unspecified on a zero divisor. -/
op% realDiv (lft rgt : real) : real := DIVISION nary

/-- Real division, left-associative; zero on a zero divisor. -/
op% realDivTotal (lft rgt : real) : real := DIVISION_TOTAL nary

/-- Euclidean integer division, left-associative; unspecified on a zero divisor. -/
op% intDiv (lft rgt : int) : int := INTS_DIVISION nary

/-- Euclidean integer division, left-associative; zero on a zero divisor. -/
op% intDivTotal (lft rgt : int) : int := INTS_DIVISION_TOTAL nary

/-- Euclidean integer modulus, never negative; unspecified on a zero divisor. -/
op% intMod (lft rgt : int) : int := INTS_MODULUS infixl "%" 70

/-- Euclidean integer modulus; the dividend on a zero divisor. -/
op% intModTotal (lft rgt : int) : int := INTS_MODULUS_TOTAL

/-- Exponentiation. -/
op% pow {α : IsArith} (base exponent : α) : α := POW

/-- Two raised to a non-negative `exponent`. -/
op% pow2 (exponent : int) : int := POW2

/-- Base-two logarithm. -/
op% log2 (arg : int) : int := LOG2

/-- Square root. -/
op% sqrt (arg : real) : real := SQRT

/-- The exponential function. -/
op% exp (arg : real) : real := EXPONENTIAL

/-- Conversion to a real. -/
op% toReal {α : IsArith} (arithTerm : α) : real := TO_REAL

/-- Conversion to an integer, rounding towards negative infinity. -/
op% toInt {α : IsArith} (arithTerm : α) : int := TO_INTEGER

/-- Bit-wise and of the low `size` bits of `lft` and `rgt`; zero when `size ≤ 0`. -/
op% piand (size lft rgt : int) : int := PIAND



/-! ## Transcendental functions -/

/-- Sine. -/
op% sine (arg : real) : real := SINE

/-- Cosine. -/
op% cosine (arg : real) : real := COSINE

/-- Tangent. -/
op% tangent (arg : real) : real := TANGENT

/-- Cosecant. -/
op% cosecant (arg : real) : real := COSECANT

/-- Secant. -/
op% secant (arg : real) : real := SECANT

/-- Cotangent. -/
op% cotangent (arg : real) : real := COTANGENT

/-- Arc sine. -/
op% arcsine (arg : real) : real := ARCSINE

/-- Arc cosine. -/
op% arccosine (arg : real) : real := ARCCOSINE

/-- Arc tangent. -/
op% arctangent (arg : real) : real := ARCTANGENT

/-- Arc cosecant. -/
op% arccosecant (arg : real) : real := ARCCOSECANT

/-- Arc secant. -/
op% arcsecant (arg : real) : real := ARCSECANT

/-- Arc cotangent. -/
op% arccotangent (arg : real) : real := ARCCOTANGENT



/-! ## Indexed operators -/

/-- Whether `arg` is divisible by `divisor`. -/
op% divisible [divisor] (arg : int) : bool := DIVISIBLE

/-- Bit-wise and of the low `size` bits of `lft` and `rgt`. -/
op% iand [size] (lft rgt : int) : int := IAND

/-! ## Constants -/

/-- The constant π. -/
op% pi : real := PI tm mkPi
