/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped

public meta import Cvc.Untyped



/-! # A tour of the sort-erased API

Terms here carry no Lean type: a `Term` is a `Term` whatever its SMT sort, and a mistake about
sorts is a *runtime* error from cvc5. What you get in exchange is that nothing has to be said
twice — no index to write down, no `ToTyp` to satisfy.

`open Cvc.Untyped` selects this layer, and with it the `smt!` spelling that expands to
`Cvc.Untyped.Term.…`.
-/
namespace Cvc.Examples.Untyped.Tour

open Cvc Untyped

variable [Ω]



/-! ## Booleans and integers

`smt!` is Lean-shaped: the operators are the ones you would write in Lean, at Lean's precedences.
`![…]` escapes back to a Lean term when you have one already.
-/

/-- info:
and     : (and a b)
implies : (=> a b)
nary    : (and a b (not a))
arith   : (+ i (* 2 j))
compare : (and (<= i j) (distinct i 0))
ite     : (ite a i j)
let     : (let ((_let_1 (+ i j))) (* _let_1 _let_1))
escape  : (+ 7 i)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Term.mkSymbolAs Bool "a"
  let b ← Term.mkSymbolAs Bool "b"
  let i ← Term.mkSymbolAs Int "i"
  let j ← Term.mkSymbolAs Int "j"

  println! "and     : {← smt! a ∧ b}"
  println! "implies : {← smt! a → b}"
  println! "nary    : {← smt! ∧[a, b, ¬ a]}"
  println! "arith   : {← smt! i + 2 * j}"
  println! "compare : {← smt! i ≤ j ∧ i ≠ 0}"
  println! "ite     : {← smt! if a then i else j}"
  println! "let     : {← smt! let s ← i + j; s * s}"
  println! "escape  : {← smt! ![Term.mkInt 7] + i}"



/-! ## Datatypes

A datatype sort is *declared*, and declaring twice gives two different sorts, so the sort is made
once and kept. `smt! match` binds each constructor's fields for you.
-/

/-- Declares `Lst := nil | cons (head : Int) (tail : Lst)`. -/
def declareLst : Env Srt := do
  let nil ← Datatype.Ctor.Decl.mk "nil"
  let cons ← Datatype.Ctor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let mut decl ← Datatype.Decl.mk "Lst"
  decl ← decl.addCtor nil
  decl ← decl.addCtor cons
  Srt.datatype decl

/-- info:
value   : (cons 1 nil)
match   : (match l (((cons h t) (* h 2)) (nil 0)))
-/
#guard_msgs in #eval Env.runIO do
  let lst ← declareLst
  let l ← Term.mkSymbol lst "l"

  -- building a value, through the constructor the sort reflects to
  let dt ← lst.getDatatype
  let consC ← dt.getCtorNamed "cons"
  let nilC ← dt.getCtorNamed "nil"
  let one ← consC.apply #[← Term.mkInt 1, ← nilC.apply]
  println! "value   : {one}"

  -- and taking one apart, by matching
  println! "match   : {← smt!
    match l with
    | cons h t => h * 2
    | nil => 0}"



/-! ## Bit-vectors

The bit-vector operators borrow Lean's own symbols, so an expression reads the same in either
language.
-/

/-- info:
and     : (bvand u v)
shift   : (bvshl u v)
literal : #b00001011
concat  : (_ BitVec 16)
-/
#guard_msgs in #eval Env.runIO do
  let u ← Term.mkSymbolAs (BitVec 8) "u"
  let v ← Term.mkSymbolAs (BitVec 8) "v"

  println! "and     : {← smt! u &&& v}"
  println! "shift   : {← smt! u <<< v}"
  println! "literal : {← Term.mkBitVec 8 0b1011}"
  -- a size is part of the sort, so concatenation changes it
  println! "concat  : {← (← Term.bvConcat u v).getSort}"



/-! ## Solving, and reading a model

`checkSat` splits the world in three, and a query only makes sense in one of them: `getValue` is
available where the answer was sat and nowhere else.
-/

/-- info:
i = 7
j = 3
u = 0x0a#8
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let i ← s.declareConst "i" (← Srt.int)
  let j ← s.declareConst "j" (← Srt.int)
  let u ← s.declareConst "u" (← Srt.bitVec 8)

  smt! i + j = 10 >>= s.assert
  smt! i - j = 4 >>= s.assert
  smt! u &&& ![Term.mkBitVec 8 0x0f] = ![Term.mkBitVec 8 0x0a] >>= s.assert

  s.checkSat (ifSat := do
    println! "i = {← s.getValueAs Int i}"
    println! "j = {← s.getValueAs Int j}"
    println! "u = {← s.getValueAs (BitVec 8) u}")
