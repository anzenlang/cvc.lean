/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Float
import Cvc.Typed.Core.Bool
import Cvc.Typed.Theory.BitVec

public meta import Cvc.Typed.Theory.Float
public meta import Cvc.Typed.Core.Bool
public meta import Cvc.Typed.Theory.BitVec



/-! # Generated Float constructors, typed -/
namespace Cvc.Tests.Typed.Term.Float

open Cvc
open Cvc.Typed.Term

/-- info:
eq        : (fp.eq f g)
lt        : (fp.lt f g)
le        : (fp.leq f g)
gt        : (fp.gt f g)
ge        : (fp.geq f g)
isNormal  : (fp.isNormal f)
isSubnorm : (fp.isSubnormal f)
isZero    : (fp.isZero f)
isInf     : (fp.isInfinite f)
isNan     : (fp.isNaN f)
isNeg     : (fp.isNegative f)
isPos     : (fp.isPositive f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Typed.Term.mkSymbolAs (Cvc.Float 8 24) "f"
  let g ← Cvc.Typed.Term.mkSymbolAs (Cvc.Float 8 24) "g"

  println! "eq        : {← fpEq f g}"
  println! "lt        : {← fpLt f g}"
  println! "le        : {← fpLe f g}"
  println! "gt        : {← fpGt f g}"
  println! "ge        : {← fpGe f g}"
  println! "isNormal  : {← fpIsNormal f}"
  println! "isSubnorm : {← fpIsSubnormal f}"
  println! "isZero    : {← fpIsZero f}"
  println! "isInf     : {← fpIsInf f}"
  println! "isNan     : {← fpIsNan f}"
  println! "isNeg     : {← fpIsNeg f}"
  println! "isPos     : {← fpIsPos f}"

/-! ## Arithmetic and conversions -/

/-- info:
abs   : (fp.abs f)
neg   : (fp.neg f)
add   : (fp.add roundNearestTiesToEven f g)
sub   : (fp.sub roundNearestTiesToEven f g)
mul   : (fp.mul roundNearestTiesToEven f g)
div   : (fp.div roundNearestTiesToEven f g)
fma   : (fp.fma roundNearestTiesToEven f g f)
sqrt  : (fp.sqrt roundNearestTiesToEven f)
rti   : (fp.roundToIntegral roundNearestTiesToEven f)
rem   : (fp.rem f g)
min   : (fp.min f g)
max   : (fp.max f g)
toReal: (fp.to_real f)
ofBits: (fp sgn ex sig)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Typed.Term.mkSymbolAs (Cvc.Float 8 24) "f"
  let g ← Cvc.Typed.Term.mkSymbolAs (Cvc.Float 8 24) "g"
  let rm ← Cvc.Typed.Term.mkRoundingMode .nearestTiesToEven
  let sgn ← Cvc.Typed.Term.mkSymbolAs (BitVec 1) "sgn"
  let ex ← Cvc.Typed.Term.mkSymbolAs (BitVec 8) "ex"
  let sig ← Cvc.Typed.Term.mkSymbolAs (BitVec 23) "sig"

  println! "abs   : {← fpAbs f}"
  println! "neg   : {← fpNeg f}"
  println! "add   : {← fpAdd rm f g}"
  println! "sub   : {← fpSub rm f g}"
  println! "mul   : {← fpMul rm f g}"
  println! "div   : {← fpDiv rm f g}"
  println! "fma   : {← fpFma rm f g f}"
  println! "sqrt  : {← fpSqrt rm f}"
  println! "rti   : {← fpRti rm f}"
  println! "rem   : {← fpRem f g}"
  println! "min   : {← fpMin f g}"
  println! "max   : {← fpMax f g}"
  println! "toReal: {← fpToReal f}"
  println! "ofBits: {← fpOfBits sgn ex sig}"

/-! ## Indexed conversions -/

/-- info:
ofIeeeBv: ((_ to_fp 8 24) w)
ofFp    : ((_ to_fp 5 11) roundNearestTiesToEven f)
ofReal  : ((_ to_fp 8 24) roundNearestTiesToEven r)
ofSbv   : ((_ to_fp 8 24) roundNearestTiesToEven u)
ofUbv   : ((_ to_fp_unsigned 8 24) roundNearestTiesToEven u)
toSbv   : ((_ fp.to_sbv 8) roundNearestTiesToEven f)
toUbv   : ((_ fp.to_ubv 8) roundNearestTiesToEven f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Typed.Term.mkSymbolAs (Cvc.Float 8 24) "f"
  let r ← Cvc.Typed.Term.mkSymbolAs (Rat) "r"
  let rm ← Cvc.Typed.Term.mkRoundingMode .nearestTiesToEven
  let w ← Cvc.Typed.Term.mkSymbolAs (BitVec 32) "w"
  let u ← Cvc.Typed.Term.mkSymbolAs (BitVec 4) "u"

  println! "ofIeeeBv: {← fpOfIeeeBv 8 24 w}"
  println! "ofFp    : {← fpOfFp 5 11 rm f}"
  println! "ofReal  : {← fpOfReal 8 24 rm r}"
  println! "ofSbv   : {← fpOfSbv 8 24 rm u}"
  println! "ofUbv   : {← fpOfUbv 8 24 rm u}"
  println! "toSbv   : {← fpToSbv 8 rm f}"
  println! "toUbv   : {← fpToUbv 8 rm f}"

/-! ## Constructors

The exponent and significand sizes are indices, so they are explicit and also fix the result's own
sizes.
-/

/-- info:
mkFloatNaN     : (fp #b0 #b11111111 #b10000000000000000000000)
mkFloatPosInf  : (fp #b0 #b11111111 #b00000000000000000000000)
mkFloatNegInf  : (fp #b1 #b11111111 #b00000000000000000000000)
mkFloatPosZero : (fp #b0 #b00000000 #b00000000000000000000000)
mkFloatNegZero : (fp #b1 #b00000000 #b00000000000000000000000)
mkFloat        : (fp #b0 #b00000000 #b00000000000000000000001)
-/
#guard_msgs in #eval Env.runIO do
  println! "mkFloatNaN     : {← mkFloatNaN 8 24}"
  println! "mkFloatPosInf  : {← mkFloatPosInf 8 24}"
  println! "mkFloatNegInf  : {← mkFloatNegInf 8 24}"
  println! "mkFloatPosZero : {← mkFloatPosZero 8 24}"
  println! "mkFloatNegZero : {← mkFloatNegZero 8 24}"
  let bv ← mkBitVec 32 1
  println! "mkFloat        : {← mkFloat 8 24 bv}"
