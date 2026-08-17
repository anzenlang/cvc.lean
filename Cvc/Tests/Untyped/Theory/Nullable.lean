/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core
import Cvc.Untyped.Theory
import Cvc.Untyped.Solver

public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory
public meta import Cvc.Untyped.Solver



/-! # Nullable constructors, sort-erased

cvc5's `Nullable` is the `Option` sort. It is a *structural* sort constructor, so `Srt.nullable`
rebuilds the same sort every time — which is what lets `ToTyp (Option α)` exist at all, a declared
datatype having no such property.
-/
namespace Cvc.Tests.Untyped.Term.Nullable

open Cvc
open Cvc.Untyped



/-! ## The sort is structural

Two builds of the same nullable sort give the *same* sort, unlike a declared datatype. Rebuilding
from `Typ` gives it back too, which is what `Srt.of (Option α)` relies on.
-/

/-- info:
sort      : (Nullable Int)
rebuilt   : true
from index: (Nullable Int)
nested    : (Nullable (Nullable Int))
of Set    : (Nullable (Set Int))
element   : Int
isNullable: true
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let srt ← Srt.nullable int
  println! "sort      : {srt}"
  println! "rebuilt   : {srt == (← Srt.nullable int)}"
  println! "from index: {← Srt.of (Option Int)}"
  println! "nested    : {← Srt.of (Option (Option Int))}"
  println! "of Set    : {← Srt.of (Option (Cvc.Set Int))}"
  println! "element   : {← srt.getNullableElementSort}"
  println! "isNullable: {srt.isNullable}"



/-! ## Constructors -/

/-- info:
null    : (as nullable.null (Nullable Int))
some 3  : (nullable.some 3)
val     : (nullable.val (nullable.some 3))
isNull  : (nullable.is_null (nullable.some 3))
isSome  : (nullable.is_some (nullable.some 3))
sort    : (Nullable Int)
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let three ← Term.mkInt 3
  let some3 ← Term.nullableSome three
  -- the *element* sort, as every constructor of a polymorphic sort takes
  println! "null    : {← Term.mkNull int}"
  println! "some 3  : {some3}"
  println! "val     : {← Term.nullableVal some3}"
  println! "isNull  : {← Term.nullableIsNull some3}"
  println! "isSome  : {← Term.nullableIsSome some3}"
  println! "sort    : {← some3.getSort}"



/-! ## Values

A nullable value is its constructor applied to nothing or to one element, so the reader walks the
term's kind and children. Unlike a set or a sequence, that works on a *built* term as well as on a
model's answer.
-/

/-- info:
some 3  → (nullable.some 3) → (some 3)
none    → (as nullable.null (Nullable Int)) → none
nested  → (nullable.some (nullable.some 3)) → (some (some 3))
inner ∅ → (nullable.some (as nullable.null (Nullable Int))) → (some none)
-/
#guard_msgs in #eval Env.runIO do
  let roundTrip (value : Option Int) : Env String := do
    let term ← Term.mkValue value
    let back : Option Int ← Term.getValue term
    return s!"{term} → {back}"
  println! "some 3  → {← roundTrip (some 3)}"
  println! "none    → {← roundTrip none}"

  let nested (value : Option (Option Int)) : Env String := do
    let term ← Term.mkValue value
    let back : Option (Option Int) ← Term.getValue term
    return s!"{term} → {back}"
  println! "nested  → {← nested (some (some 3))}"
  println! "inner ∅ → {← nested (some none)}"

/-- info:
built some : true
built null : true
symbol     : false
element    : false
rejected   : expected a nullable value, got `x`
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let some3 ← Term.mkValue (some 3 : Option Int)
  let nullT ← Term.mkValue (none : Option Int)
  -- nullable-sorted but not a value: a declared constant stands for one without being one
  let x ← s.declareConst "x" (← Srt.of (Option Int))
  println! "built some : {← Term.isNullableValue some3}"
  println! "built null : {← Term.isNullableValue nullT}"
  println! "symbol     : {← Term.isNullableValue x}"
  -- and neither is the element of one, which has the element's sort
  println! "element    : {← Term.isNullableValue (← Term.nullableVal some3)}"
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"
  println! "rejected   : {← caught do
    let v : Option Int ← Term.getValue x
    pure s!"{v}"}"



/-! ## Through a model -/

/-- info:
x : (some 7)
y : none
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let srt ← Srt.of (Option Int)
  let x ← s.declareConst "x" srt
  let y ← s.declareConst "y" srt
  (do Term.nullableIsSome x) >>= s.assert
  (do Term.equal (← Term.nullableVal x) (← Term.mkInt 7)) >>= s.assert
  (do Term.nullableIsNull y) >>= s.assert
  s.checkSat (ifSat := do
    println! "x : {← s.getValueAs (Option Int) x}"
    println! "y : {← s.getValueAs (Option Int) y}")
