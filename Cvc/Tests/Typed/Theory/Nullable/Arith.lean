/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Nullable.Arith
import Cvc.Typed.Theory.Arith
import Cvc.Typed.Solver

public meta import Cvc.Typed.Theory.Nullable.Arith
public meta import Cvc.Typed.Theory.Arith
public meta import Cvc.Typed.Solver



/-! # Generated arithmetic over nullables, typed

A lifted operator has its plain counterpart's signature with an `Option` around every argument and
around the result, and nothing else changed — the same type variables, the same `IsArith`, the same
side condition on the n-ary form.

The lift is **strict**: `none` unless every argument is `some`. That is `nullable.lift`'s semantics
rather than a choice made here, and it is why `equal?` is not `Option`'s own equality — `equal?` of
two `none`s is `none`, not `some true`.
-/
namespace Cvc.Tests.Typed.Term.Nullable.Arith

open Cvc
open Cvc.Typed (Term Terms Solver)
open Cvc.Typed.Term



/-! ## Signatures

The `Option` wrapping is the only difference from the plain operator, so a lifted operator is as
constrained as the one it lifts.
-/

/-- info: @add? : [inst : Ω] →
  {α : Type} → [inst_1 : ToTyp α] → [IsArith α] → Term (Option α) → Term (Option α) → Env (Term (Option α)) -/
#guard_msgs in #check @Cvc.Typed.Term.add?

/-- info: @addN? : [inst : Ω] →
  {α : Type} →
    [inst_1 : ToTyp α] →
      [IsArith α] → (terms : Terms (Option α)) → autoParam (2 ≤ Array.size terms) addN?._auto_1 → Env (Term (Option α)) -/
#guard_msgs in #check @Cvc.Typed.Term.addN?

section indices
variable [Ω] (x y : Term (Option Int)) (r : Term (Option Rat)) (i : Term Int)

/-- A comparison answers at `Option Bool`, as its plain counterpart answers at `Bool`. -/
example : Env (Term (Option Bool)) := lt? x y
/-- A conversion carries its result index through the `Option`. -/
example : Env (Term (Option Rat)) := toReal? x
/-- Arithmetic stays at the argument's index. -/
example : Env (Term (Option Int)) := add? x y

/-- error: Application type mismatch: The argument
  i
has type
  Term Int
but is expected to have type
  Term (Option ?m.10)
in the application
  i.add?

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in example := add? i i

-- the lift does not nest: `Option (Option Int)` is not arithmetic, so there is no instance
/-- error: failed to synthesize instance of type class
  IsArith (Option Int)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in example [Ω] (n : Term (Option (Option Int))) : Env (Term (Option (Option Int))) :=
  add? n n

end indices



/-! ## Solving -/

/-- info:
3 + 4     : (some 7)
3 + 4 + ⊥ : none
3 < 4     : (some true)
⊥ < 4     : none
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst (Option Int) "x"
  let y ← s.declareConst (Option Int) "y"
  let z ← s.declareConst (Option Int) "z"

  -- dot notation works through the `?`
  let sum ← x.add? y
  let sumN ← addN? #[x, y, z]
  let lt ← lt? x y
  let ltNull ← lt? z y

  (do equal x (← nullableSome (← mkInt 3))) >>= s.assert
  (do equal y (← nullableSome (← mkInt 4))) >>= s.assert
  (do nullableIsNull z) >>= s.assert

  s.checkSat (ifSat := do
    println! "3 + 4     : {← s.getValue sum}"
    println! "3 + 4 + ⊥ : {← s.getValue sumN}"
    println! "3 < 4     : {← s.getValue lt}"
    println! "⊥ < 4     : {← s.getValue ltNull}")



/-! ## Defaulting n-ary variants

`<id>N'?` needs no side condition, defaulting the empty and one-element cases. The index has to be
stated on an empty array, exactly as it does for the plain `addN'` — there is nothing else to infer
it from.
-/

/-- info:
addN'? []   : (some 0)
addN'? [x]  : (some 5)
addN'? [x,x]: (some 10)
mulN'? []   : (some 1)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst (Option Int) "x"
  let empty : Term (Option Int) ← addN'? #[]
  let single ← addN'? #[x]
  let many ← addN'? #[x, x]
  let unit : Term (Option Int) ← mulN'? #[]
  (do equal x (← nullableSome (← mkInt 5))) >>= s.assert
  s.checkSat (ifSat := do
    println! "addN'? []   : {← s.getValue empty}"
    println! "addN'? [x]  : {← s.getValue single}"
    println! "addN'? [x,x]: {← s.getValue many}"
    println! "mulN'? []   : {← s.getValue unit}")
