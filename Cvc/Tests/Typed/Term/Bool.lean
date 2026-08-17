/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Term.Bool

public meta import Cvc.Typed.Term.Bool



/-! # Generated Boolean and sort-generic constructors, typed -/
namespace Cvc.Tests.Typed.Term.Bool

open Cvc
open Cvc.Typed (Term)
open Cvc.Typed.Term

/-- info:
and      : (and a b)
implies  : (=> a b)
not      : (not a)
equal    : (= i j)
distinct : (distinct i j)
ite bool : (ite a b a)
ite int  : (ite a i j)
andN     : (and a b a)
equalN   : (and (= i j) (= j i))
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Typed.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Typed.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Typed.Term.mkSymbolAs Int "j"

  println! "and      : {← and a b}"
  println! "implies  : {← implies a b}"
  println! "not      : {← not a}"
  println! "equal    : {← equal i j}"
  println! "distinct : {← distinct i j}"
  println! "ite bool : {← ite a b a}"
  println! "ite int  : {← ite a i j}"
  println! "andN     : {← andN #[a, b, a]}"
  println! "equalN   : {← equalN #[i, j, i]}"

section indices
variable [Ω] (a b : Term Bool) (i j : Term Int)

/-- `ite` preserves its branches' index. -/
example : Env (Term Int) := ite a i j
/-- …including at `Bool`. -/
example : Env (Term Bool) := ite a b b

end indices

/-! ## Constructors -/

/-- info:
mkTrue   : true
mkFalse  : false
mkBool   : false
-/
#guard_msgs in #eval Env.runIO do
  println! "mkTrue   : {← mkTrue}"
  println! "mkFalse  : {← mkFalse}"
  println! "mkBool   : {← mkBool false}"

/-! ## Symbols

`mkSymbol` makes a free constant, taking its sort from the index. The bound-variable constructor
is not a generated theory constructor — it produces a `BVar` rather than a `Term` — and is covered
in `Tests/{Untyped,Typed}/BVar.lean`.
-/

/-- info: mkSymbol : x -/
#guard_msgs in #eval Env.runIO do
  println! "mkSymbol : {← (mkSymbol "x" : Env (Cvc.Typed.Term Int))}"
