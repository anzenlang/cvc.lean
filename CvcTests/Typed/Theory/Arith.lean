/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Arith
import Cvc.Typed.Core.Bool

public meta import Cvc.Typed.Theory.Arith
public meta import Cvc.Typed.Core.Bool



/-! # Generated arithmetic constructors, typed -/
namespace Cvc.Tests.Typed.Term.Arith

open Cvc
open Cvc.Typed.Term

/-! ## Arithmetic -/

/-- info:
realDiv     : (/ r r)
realDivTotal: (/_total r r)
intDiv      : (div i j)
intDivTotal : (div_total i j)
intMod      : (mod i j)
intModTotal : (mod_total i j)
pow         : (^ i j)
pow2        : (int.pow2 i)
log2        : (int.log2 i)
sqrt        : (sqrt r)
exp         : (exp r)
toReal      : (to_real i)
toInt       : (to_int r)
piand       : (piand i i j)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Typed.Term.mkSymbolAs (Int) "j"
  let r ← Cvc.Typed.Term.mkSymbolAs (Rat) "r"

  println! "realDiv     : {← realDiv r r}"
  println! "realDivTotal: {← realDivTotal r r}"
  println! "intDiv      : {← intDiv i j}"
  println! "intDivTotal : {← intDivTotal i j}"
  println! "intMod      : {← intMod i j}"
  println! "intModTotal : {← intModTotal i j}"
  println! "pow         : {← pow i j}"
  println! "pow2        : {← pow2 i}"
  println! "log2        : {← log2 i}"
  println! "sqrt        : {← sqrt r}"
  println! "exp         : {← exp r}"
  println! "toReal      : {← toReal i}"
  println! "toInt       : {← toInt r}"
  println! "piand       : {← piand i i j}"

/-! ## Transcendental functions -/

/-- info:
sine        : (sin r)
cosine      : (cos r)
tangent     : (tan r)
cosecant    : (csc r)
secant      : (sec r)
cotangent   : (cot r)
arcsine     : (arcsin r)
arccosine   : (arccos r)
arctangent  : (arctan r)
arccosecant : (arccsc r)
arcsecant   : (arcsec r)
arccotangent: (arccot r)
-/
#guard_msgs in #eval Env.runIO do
  let r ← Cvc.Typed.Term.mkSymbolAs (Rat) "r"

  println! "sine        : {← sine r}"
  println! "cosine      : {← cosine r}"
  println! "tangent     : {← tangent r}"
  println! "cosecant    : {← cosecant r}"
  println! "secant      : {← secant r}"
  println! "cotangent   : {← cotangent r}"
  println! "arcsine     : {← arcsine r}"
  println! "arccosine   : {← arccosine r}"
  println! "arctangent  : {← arctangent r}"
  println! "arccosecant : {← arccosecant r}"
  println! "arcsecant   : {← arcsecant r}"
  println! "arccotangent: {← arccotangent r}"

/-! ## Indexed arithmetic -/

/-- info:
divisible   : ((_ divisible 3) i)
iand        : ((_ iand 8) i i)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs (Int) "i"

  println! "divisible   : {← divisible 3 i}"
  println! "iand        : {← iand 8 i i}"

/-! ## Operators shared with the connectives' block -/

/-- info:
add      : (+ i j)
mul      : (* i j)
lt       : (< i j)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Typed.Term.mkSymbolAs Int "j"

  println! "add      : {← add i j}"
  println! "mul      : {← mul i j}"
  println! "lt       : {← lt i j}"


/-! ## Predicates -/

/-- info:
isInt int : (is_int i)
isInt rat : (is_int r)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let r ← Cvc.Typed.Term.mkSymbolAs Rat "r"
  println! "isInt int : {← isInt i}"
  println! "isInt rat : {← isInt r}"

/-! ## Operators shared with the connectives' block -/

/-- info:
neg int  : (- i)
neg rat  : (- r)
leN      : (and (<= i j) (<= j i))
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Typed.Term.mkSymbolAs Int "j"
  let r ← Cvc.Typed.Term.mkSymbolAs Rat "r"

  println! "neg int  : {← neg i}"
  println! "neg rat  : {← neg r}"
  println! "leN      : {← leN #[i, j, i]}"


/-! ## Index discipline -/

section indices
open Cvc.Typed (Term)
variable [Ω] (i j : Term Int)

/-- A comparison lands in `Term Bool` whatever its arguments' index. -/
example : Env (Term Bool) := lt i j

end indices

/-! ## Constants -/

/-- info: pi : real.pi -/
#guard_msgs in #eval Env.runIO do
  println! "pi : {← pi}"

/-! ## Constructors -/

/-- info:
mkInt        : (- 3)
mkIntOfString: 42
mkReal       : (/ 2 3)
mkRealOfStr  : (/ 1 2)
-/
#guard_msgs in #eval Env.runIO do
  println! "mkInt        : {← mkInt (-3)}"
  println! "mkIntOfString: {← mkIntOfString "42"}"
  println! "mkReal       : {← mkReal (2/3 : Rat)}"
  println! "mkRealOfStr  : {← mkRealOfString "1/2"}"


/-! # The `smt!` DSL, arithmetic notation

These notations come from this theory's `op%` entries and are emitted beside its constructors, so
they exist exactly where the theory does. What the typed layer adds is the *index* the expansion
carries, pinned by the `example`s below.
-/

open Cvc.Typed in
/-- info:
add      : (+ i j)
prec     : (+ i (* j i))
paren    : (* (+ i j) i)
unary -  : (- i)
literals : (+ 3 i)
mod      : (mod i j)
left-assoc - : (- (- i j) i)
real     : (/ 3 2)
exponent : (/ 3 2000)
in expr  : (+ (/ 3 2) (/ 5 2))
with sym : (< r (/ 3 2))
-/
#guard_msgs in #eval Env.runIO do
  let i ← mkSymbolAs Int "i"
  let j ← mkSymbolAs Int "j"
  let r ← mkSymbolAs Rat "r"

  println! "add      : {← smt! i + j}"
  println! "prec     : {← smt! i + j * i}"
  println! "paren    : {← smt! (i + j) * i}"
  println! "unary -  : {← smt! - i}"
  println! "literals : {← smt! 3 + i}"
  println! "mod      : {← smt! i % j}"
  println! "left-assoc - : {← smt! i - j - i}"
  println! "real     : {← smt! 1.5}"
  println! "exponent : {← smt! 1.5e-3}"
  println! "in expr  : {← smt! 1.5 + 2.5}"
  println! "with sym : {← smt! r < 1.5}"

section indices
open Cvc.Typed
variable [Ω] (i j : Term Int) (r : Term Rat)

/-- A comparison drops from `Int` to `Bool`. -/
example : Env (Term Bool) := smt! i < j
/-- Arithmetic stays at its operands' index. -/
example : Env (Term Int) := smt! i + j * i
/-- …including over the reals. -/
example : Env (Term Rat) := smt! - r
/-- A real literal lands at `Rat`, not at `Int`. -/
example : Env (Term Rat) := smt! 1.5 + 2.5

end indices
