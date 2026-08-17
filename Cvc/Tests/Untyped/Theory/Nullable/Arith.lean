/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Nullable.Arith
import Cvc.Untyped.Core.Arith
import Cvc.Untyped.Solver

public meta import Cvc.Untyped.Theory.Nullable.Arith
public meta import Cvc.Untyped.Core.Arith
public meta import Cvc.Untyped.Solver



/-! # Generated arithmetic over nullables, sort-erased

One lifted constructor per liftable arithmetic operator, named `<id>?`. Each is `nullable.lift`
applied to the operator's kind, which is **strict**: the result is `none` unless every argument is
`some`.
-/
namespace Cvc.Tests.Untyped.Term.Nullable.Arith

open Cvc
open Cvc.Untyped

/-- A nullable-integer constant. -/
def nInt [Ω] (s : Solver) (name : String) : Env Term := do
  s.declareConst name (← Srt.nullable (← Srt.int))



/-! ## Construction

The lifted term is a `nullable.lift` of a lambda over the element sorts — cvc5 builds that lambda
from the kind, so the printed form names bound variables it introduced itself.
-/

/-- info:
add? sort : (Nullable Int)
lt?  sort : (Nullable Bool)
neg? sort : (Nullable Int)
addN? kids: 4
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let x ← nInt s "x"
  let y ← nInt s "y"
  let z ← nInt s "z"
  println! "add? sort : {← (← Term.add? x y).getSort}"
  println! "lt?  sort : {← (← Term.lt? x y).getSort}"
  println! "neg? sort : {← (← Term.neg? x).getSort}"
  -- the lambda plus one argument per nullable term
  println! "addN? kids: {(← Term.addN? #[x, y, z]).getKids.size}"

/-! The n-ary form carries the same side condition its plain counterpart does, so too few arguments
is an elaboration error rather than the malformed term cvc5 would otherwise accept.
-/

/-- error: could not synthesize default value for parameter 'atLeastTwoElements' using tactics
---
error: failed to prove term array has at least two elements
inst✝ : Ω
x : Term
⊢ 2 ≤ #[x].size
-/
#guard_msgs in
example [Ω] (x : Term) : Env Term := Term.addN? #[x]



/-! ## Solving

The lift is strict, which is what the last two lines show: one `none` argument makes the whole
result `none`, even where the operator would not need that argument's value.
-/

/-- info:
3 + 4     : (some 7)
3 + 4 + ⊥ : none
3 < 4     : (some true)
⊥ < 4     : none
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← nInt s "x"
  let y ← nInt s "y"
  let z ← nInt s "z"

  let sum ← Term.add? x y
  let sumN ← Term.addN? #[x, y, z]
  let lt ← Term.lt? x y
  let ltNull ← Term.lt? z y

  (do Term.equal x (← Term.nullableSome (← Term.mkInt 3))) >>= s.assert
  (do Term.equal y (← Term.nullableSome (← Term.mkInt 4))) >>= s.assert
  (do Term.nullableIsNull z) >>= s.assert

  s.checkSat (ifSat := do
    println! "3 + 4     : {← s.getValueAs (Option Int) sum}"
    println! "3 + 4 + ⊥ : {← s.getValueAs (Option Int) sumN}"
    println! "3 < 4     : {← s.getValueAs (Option Bool) lt}"
    println! "⊥ < 4     : {← s.getValueAs (Option Bool) ltNull}")



/-! ## Defaulting n-ary variants

`<id>N'?` defaults the empty and one-element cases as its plain counterpart does. The unit is the
plain one wrapped in `some`, since every argument and the result of a lifted operator are nullable:
`addN'? #[]` is `some 0`, not `0`.
-/

/-- info:
addN'? []    : (nullable.some 0)
addN'? [x]   : x
addN'? [x,x] sort: (Nullable Int)
mulN'? []    : (nullable.some 1)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let x ← nInt s "x"
  println! "addN'? []    : {← Term.addN'? #[]}"
  println! "addN'? [x]   : {← Term.addN'? #[x]}"
  println! "addN'? [x,x] sort: {← (← Term.addN'? #[x, x]).getSort}"
  println! "mulN'? []    : {← Term.mulN'? #[]}"
