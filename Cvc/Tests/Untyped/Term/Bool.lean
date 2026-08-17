/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Term.Bool
import Cvc.Untyped.Term.Arith
import Cvc.Untyped.Solver

public meta import Cvc.Untyped.Term.Bool
public meta import Cvc.Untyped.Term.Arith
public meta import Cvc.Untyped.Solver



/-! # Generated Boolean and sort-generic constructors, sort-erased -/
namespace Cvc.Tests.Untyped.Term.Bool

open Cvc
open Cvc.Untyped.Term

/-- info:
and      : (and a b)
or       : (or a b)
xor      : (xor a b)
not      : (not a)
implies  : (=> a b)
equal    : (= i j)
distinct : (distinct i j)
ite      : (ite a i j)
andN     : (and a b a)
andN' [] : true
andN' [x]: a
orN' []  : false
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Untyped.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Untyped.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let j ← Cvc.Untyped.Term.mkSymbolAs Int "j"

  println! "and      : {← and a b}"
  println! "or       : {← or a b}"
  println! "xor      : {← xor a b}"
  println! "not      : {← not a}"
  println! "implies  : {← implies a b}"
  println! "equal    : {← equal i j}"
  println! "distinct : {← distinct i j}"
  println! "ite      : {← ite a i j}"
  println! "andN     : {← andN #[a, b, a]}"
  println! "andN' [] : {← andN' #[]}"
  println! "andN' [x]: {← andN' #[a]}"
  println! "orN' []  : {← orN' #[]}"

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

`mkSymbol` makes a free constant of the given sort. The bound-variable constructor is not a
generated theory constructor — it produces a `BVar` rather than a `Term` — and is covered in
`Tests/{Untyped,Typed}/BVar.lean`.
-/

/-- info: mkSymbol : x -/
#guard_msgs in #eval Env.runIO do
  println! "mkSymbol : {← mkSymbol (← Srt.of Int) "x"}"
