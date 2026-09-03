/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed

public meta import Cvc.Typed



/-! # A tour of the typed API

The same terms as the sort-erased tour, with one difference that runs through everything: a term
carries the Lean type its SMT sort denotes. `Term Int` and `Term Bool` are different types, so a
sort mistake is a *Lean* error at the point it is written rather than a cvc5 error at check-sat,
and a value read out of a model comes back as the Lean type it should be with nothing to convert.

`open Cvc.Typed` selects this layer, and with it the `smt!` spelling that expands to
`Cvc.Typed.Term.…`.
-/
namespace Cvc.Examples.Typed.Tour

open Cvc Typed

variable [Ω]



/-! ## Booleans and integers

The DSL is the same; what it produces is indexed. Each `example` below pins the index its
expansion carries — none of them is ascribed, all of them are inferred.
-/

/-- info:
and     : (and a b)
nary    : (and a b (not a))
arith   : (+ i (* 2 j))
compare : (and (<= i j) (distinct i 0))
ite     : (ite a i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Term.mkSymbolAs Bool "a"
  let b ← Term.mkSymbolAs Bool "b"
  let i ← Term.mkSymbolAs Int "i"
  let j ← Term.mkSymbolAs Int "j"

  println! "and     : {← smt! a ∧ b}"
  println! "nary    : {← smt! ∧[a, b, ¬ a]}"
  println! "arith   : {← smt! i + 2 * j}"
  println! "compare : {← smt! i ≤ j ∧ i ≠ 0}"
  println! "ite     : {← smt! if a then i else j}"

section indices
variable (a : Term Bool) (i j : Term Int)

/-- A connective stays at `Bool`. -/
example : Env (Term Bool) := smt! a ∧ ¬ a
/-- Arithmetic stays at its operands' index. -/
example : Env (Term Int) := smt! i + 2 * j
/-- A comparison drops to `Bool`. -/
example : Env (Term Bool) := smt! i ≤ j
/-- And `ite` takes its index from its branches. -/
example : Env (Term Int) := smt! if a then i else j

end indices

/-! A sort mistake does not compile, where sort-erased it is a cvc5 error at check-sat. -/

/--
error: Application type mismatch: The argument
  i
has type
  Term Int
but is expected to have type
  Term Bool
in the application
  a.and i

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example (a : Term Bool) (i : Term Int) : Env (Term Bool) := Term.and a i



/-! ## Datatypes

A declared sort is fresh, so it cannot be rebuilt from a description — it is looked up by name in
the scope's registry, and a Lean type is bound to that name by a `ToTyp` instance. From there the
datatype's index is first-class: `Term Lst` is a term like any other.
-/

/-- The Lean index standing for the SMT datatype `Lst`. -/
structure Lst where private mk ::
  deriving DecidableEq, Ord, Hashable

instance : ToTyp Lst := ⟨.datatype "Lst"⟩

/-- Declares `Lst := nil | cons (head : Int) (tail : Lst)`. -/
def declareLst : Env Srt := do
  let nil ← Cvc.Datatype.Ctor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Ctor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Datatype.Decl.mk "Lst"
  Srt.datatype (← (← decl.addCtor nil).addCtor cons)

/-- info:
value   : (cons 1 nil)
head    : (head (cons 1 nil))
is cons : ((_ is cons) l)
match   : (match l (((cons h t) (* h 2)) (nil 0)))
-/
#guard_msgs in #eval Env.runIO do
  let _ ← declareLst
  let l ← Term.mkSymbolAs Lst "l"

  -- a constructor is found by name and checked once; the handle carries the index from there
  let consC ← Datatype.ctor Lst "cons"
  let nilC ← Datatype.ctor Lst "nil"
  let head ← consC.field Int "head"

  let one ← consC.apply2 (← Term.mkInt 1) (← nilC.apply)
  println! "value   : {one}"
  println! "head    : {← head.get one}"
  println! "is cons : {← consC.is l}"

  -- a match binds each constructor's fields, and only the ones the body names are re-typed
  println! "match   : {← smt!
    match l with
    | cons h t => h * 2
    | nil => 0}"



/-! ## Bit-vectors

A bit-vector's **width is in the index**, so an operation that changes it says so in its type:
`bvConcat` on two `Term (BitVec 8)` answers a `Term (BitVec 16)`, computed rather than checked.
-/

/-- info:
and     : (bvand u v)
shift   : (bvshl u v)
literal : #b00001011
-/
#guard_msgs in #eval Env.runIO do
  let u ← Term.mkSymbolAs (BitVec 8) "u"
  let v ← Term.mkSymbolAs (BitVec 8) "v"

  println! "and     : {← smt! u &&& v}"
  println! "shift   : {← smt! u <<< v}"
  println! "literal : {← Term.mkBitVec 8 0b1011}"

section widths
variable (u v : Term (BitVec 8))

/-- The width is preserved by the bitwise operators… -/
example : Env (Term (BitVec 8)) := smt! u &&& v
/-- …and *added* by concatenation, in the index. -/
example : Env (Term (BitVec 16)) := Term.bvConcat u v

end widths



/-! ## Solving, and reading a model

`declareConst` takes the Lean type, so the term it answers is indexed and `getValue` needs no
target type: what comes back is an `Int`, a `Bool`, a `BitVec 8`.
-/

/-- info:
i = 7, j = 3, u = 0x0a#8
and they are Lean values: 10, 10
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let i ← s.declareConst Int "i"
  let j ← s.declareConst Int "j"
  let u ← s.declareConst (BitVec 8) "u"

  (← smt! i + j = 10) |> s.assert
  (← smt! i - j = 4) |> s.assert
  (← smt! ![pure u] &&& ![Term.mkBitVec 8 0x0f] = ![Term.mkBitVec 8 0x0a]) |> s.assert

  s.checkSat (ifSat := do
    let i : Int ← s.getValue i
    let j : Int ← s.getValue j
    let u : BitVec 8 ← s.getValue u
    println! "i = {i}, j = {j}, u = {u}"
    println! "and they are Lean values: {i + j}, {u.toNat}")
