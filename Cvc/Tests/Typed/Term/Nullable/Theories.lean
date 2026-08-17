/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Term
import Cvc.Typed.Solver

public meta import Cvc.Typed.Term
public meta import Cvc.Typed.Solver



/-! # Lifted operators across the theories, typed

Arithmetic is covered on its own in `Nullable/Arith.lean`; this samples the other theories, whose
lifts come from the same generator and differ only in what the specification says.

The rule everywhere: an `Option` around every argument and around the result, nothing else changed.
So a *container's term* becomes nullable, never its elements — `Option (Set α)` rather than
`Set (Option α)`.
-/
namespace Cvc.Tests.Typed.Term.Nullable.Theories

open Cvc
open Cvc.Typed (Term Solver)
open Cvc.Typed.Term



/-! ## The shape of a lifted signature -/

section signatures
variable [Ω]

/-- Boolean, with the sort-generic operators taking whatever index they are given. -/
example (a b : Term (Option Bool)) : Env (Term (Option Bool)) := and? a b
/-- `ite?` is strict in its condition too, so every argument is nullable. -/
example (c : Term (Option Bool)) (x y : Term (Option Int)) : Env (Term (Option Int)) := ite? c x y
/-- Bit-vectors keep their size index. -/
example (x y : Term (Option (BitVec 8))) : Env (Term (Option (BitVec 8))) := bvAdd? x y
/-- Strings. -/
example (x y : Term (Option String)) : Env (Term (Option String)) := strConcat? x y
/-- A set's *term* is what becomes nullable; its element type is untouched. -/
example (e : Term (Option Int)) (s : Term (Option (Cvc.Set Int)))
: Env (Term (Option Bool)) := setMember? e s
/-- Likewise an array's. -/
example (a : Term (Option (Cvc.TotalMap Int Bool))) (i : Term (Option Int))
: Env (Term (Option Bool)) := select? a i
/-- A rounding mode becomes nullable along with the operands. -/
example (r : Term (Option Cvc.Float.RoundingMode)) (x y : Term (Option (Cvc.Float 8 24)))
: Env (Term (Option (Cvc.Float 8 24))) := fpAdd? r x y

end signatures



/-! ## Solving

`equal?` is the one to watch: the lift is strict, so it is **not** `Option`'s equality — two `none`s
compare to `none`, not to `some true`.
-/

/-- info:
"ab" ++ "c" : (some abc)
8 + 1 (bv)  : (some 0x09#8)
equal ⊥ ⊥   : none
and true ⊥  : none
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let a ← nullableSome (← mkString "ab" false)
  let c ← nullableSome (← mkString "c" false)
  let cat ← strConcat? a c

  let bv ← nullableSome (← mkBitVec (size := 8) 8)
  let one ← nullableSome (← mkBitVec (size := 8) 1)
  let sum ← bvAdd? bv one

  let n ← s.declareConst (Option Int) "n"
  (do nullableIsNull n) >>= s.assert
  let eq ← equal? n n
  let andT ← and? (← nullableSome (← mkTrue)) (← mkNull' Bool)

  s.checkSat (ifSat := do
    println! "\"ab\" ++ \"c\" : {← s.getValue cat}"
    println! "8 + 1 (bv)  : {← s.getValue sum}"
    println! "equal ⊥ ⊥   : {← s.getValue eq}"
    println! "and true ⊥  : {← s.getValue andT}")
