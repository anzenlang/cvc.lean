/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core.Bool

public meta import Cvc.Typed.Core.Bool



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


/-! # The `smt!` DSL, boolean notation

These notations come from this theory's `op%` entries and are emitted beside its constructors, so
they exist exactly where the theory does. What the typed layer adds is the *index* the expansion
carries, pinned by the `example`s below.
-/

open Cvc.Typed in
/-- info:
and      : (and a b)
or       : (or a b)
xor      : (xor a b)
implies  : (=> a b)
not      : (not a)
equal    : (= i j)
distinct : (distinct i j)
nary and : (and a b a)
nary eq  : (and (= i j) (= j i))
bool lit : (and a true)
ite      : (ite a i j)
right-assoc ∧ : (and a (and b a))
-/
#guard_msgs in #eval Env.runIO do
  let a ← mkSymbolAs Bool "a"
  let b ← mkSymbolAs Bool "b"
  let i ← mkSymbolAs Int "i"
  let j ← mkSymbolAs Int "j"

  println! "and      : {← smt! a ∧ b}"
  println! "or       : {← smt! a ∨ b}"
  println! "xor      : {← smt! a ⊻ b}"
  println! "implies  : {← smt! a → b}"
  println! "not      : {← smt! ¬ a}"
  println! "equal    : {← smt! i = j}"
  println! "distinct : {← smt! i ≠ j}"
  println! "nary and : {← smt! ∧[a, b, a]}"
  println! "nary eq  : {← smt! =[i, j, i]}"
  println! "bool lit : {← smt! a ∧ true}"
  println! "ite      : {← smt! if a then i else j}"
  println! "right-assoc ∧ : {← smt! a ∧ b ∧ a}"

section indices
open Cvc.Typed
variable [Ω] (a b : Term Bool) (i j : Term Int)

/-- A connective stays at `Bool`. -/
example : Env (Term Bool) := smt! a ∧ b
/-- `ite` takes its index from its branches. -/
example : Env (Term Int) := smt! if a then i else j
/-- An n-ary equality over `Int` still lands in `Bool`. -/
example : Env (Term Bool) := smt! =[i, j, i]

end indices
