/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Solver

public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Solver



/-! # Nullable constructors, typed

cvc5's `Nullable` is denoted by Lean's `Option`, so a nullable term is a `Term (Option α)` and its
element a `Term α`. The index is what tells `mkNull` which sort to build, where the sort-erased
version takes the element sort.
-/
namespace Cvc.Tests.Typed.Term.Nullable

open Cvc
open Cvc.Typed (Term Solver)
open Cvc.Typed.Term



/-! ## Constructors -/

/-- info:
null    : (as nullable.null (Nullable Int))
some 3  : (nullable.some 3)
val     : (nullable.val (nullable.some 3))
isNull  : (nullable.is_null (nullable.some 3))
isSome  : (nullable.is_some (nullable.some 3))
nested  : (nullable.some (nullable.some 3))
-/
#guard_msgs in #eval Env.runIO do
  let some3 ← nullableSome (← mkInt 3)
  println! "null    : {(← mkNull' Int).erase}"
  println! "some 3  : {some3.erase}"
  println! "val     : {(← nullableVal some3).erase}"
  println! "isNull  : {(← nullableIsNull some3).erase}"
  println! "isSome  : {(← nullableIsSome some3).erase}"
  println! "nested  : {(← nullableSome some3).erase}"

/-! The index tracks the element, so nothing needs re-typing to be used. -/

section indices
variable [Ω] (n : Term (Option Int)) (i : Term Int)

/-- `nullableSome` wraps the index in `Option`. -/
example : Env (Term (Option Int)) := nullableSome i
/-- `nullableVal` takes it back off. -/
example : Env (Term Int) := nullableVal n
/-- …so its result is an arithmetic term like any other. -/
example : Env (Term Int) := do add (← nullableVal n) i
/-- The predicates answer at `Bool`. -/
example : Env (Term Bool) := nullableIsSome n
/-- And they nest, `Option (Option Int)` being an ordinary index. -/
example : Env (Term (Option (Option Int))) := nullableSome n

/-- info: @nullableVal : [inst : Ω] → {α : Type} → Term (Option α) → Env (Term α) -/
#guard_msgs in #check @Cvc.Typed.Term.nullableVal

/-- error: Application type mismatch: The argument
  i
has type
  Term Int
but is expected to have type
  Term (Option ?m.6)
in the application
  i.nullableVal

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in example := nullableVal i

end indices



/-! ## Values

`Option α` is the value type, so the conversion is the identity on the Lean side and the round trip
carries the index across.
-/

/-- info:
some 3  : (nullable.some 3) → (some 3)
none    : (as nullable.null (Nullable Int)) → none
nested  : (nullable.some (nullable.some 3)) → (some (some 3))
inner ∅ : (nullable.some (as nullable.null (Nullable Int))) → (some none)
of Bool : (nullable.some true) → (some true)
-/
#guard_msgs in #eval Env.runIO do
  let roundTrip (α : Type) [Cvc.Typed.SrtLike α] (value : Option α) [ToString α]
  : Env String := do
    let term : Term (Option α) ← mkValue value
    let back : Option α ← getValue term
    return s!"{term.erase} → {back}"
  println! "some 3  : {← roundTrip Int (some 3)}"
  println! "none    : {← roundTrip Int none}"
  println! "nested  : {← roundTrip (Option Int) (some (some 3))}"
  println! "inner ∅ : {← roundTrip (Option Int) (some none)}"
  println! "of Bool : {← roundTrip Bool (some true)}"



/-! ## Through a model

`Option` goes wherever an index goes, so a nullable is declarable, assertable and readable like any
other sort — including as the element of a container.
-/

/-- info:
x     : (some 7)
y     : none
inSet : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst (Option Int) "x"
  let y ← s.declareConst (Option Int) "y"
  (do nullableIsSome x) >>= s.assert
  (do equal (← nullableVal x) (← mkInt 7)) >>= s.assert
  (do nullableIsNull y) >>= s.assert

  -- an `Option` index nests in a container, which is what a structural sort buys
  let set ← s.declareConst (Cvc.Set (Option Int)) "set"
  (do setMember x set) >>= s.assert

  s.checkSat (ifSat := do
    println! "x     : {← s.getValue x}"
    println! "y     : {← s.getValue y}"
    let elems : Cvc.Set (Option Int) ← s.getValue set
    println! "inSet : {elems.contains (some 7)}")
