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



/-! # Values, typed

The same round trip as the sort-erased layer, except that the index picks the instance: no type has
to be named at a call site, because the term already says which one applies.
-/
namespace Cvc.Tests.Typed.Value

open Cvc
open Cvc.Typed



/-! ## The index picks the instance

Nothing below names a type. `mkValue` is resolved by the value's own Lean type, and `getValue` by
the term's index, so the two are forced to agree.
-/

/-- info:
Bool   : true
Int    : -7
Rat    : -3/4
String : hello world
BitVec : 0x0a#8
-/
#guard_msgs in #eval Env.runIO do
  println! "Bool   : {← Term.extractValue (← Term.mkValue true)}"
  println! "Int    : {← Term.extractValue (← Term.mkValue (-7 : Int))}"
  println! "Rat    : {← Term.extractValue (← Term.mkValue (-3/4 : Rat))}"
  println! "String : {← Term.extractValue (← Term.mkValue "hello world")}"
  println! "BitVec : {← Term.extractValue (← Term.mkValue (10 : BitVec 8))}"

-- and the reader's index is what makes a mismatch impossible to write: `getBoolValue` takes a
-- `Term Bool` and nothing else
section discipline
variable [Ω] (b : Term Bool) (i : Term Int) (bv : Term (BitVec 8))

example : Res Bool := Term.getBoolValue b
example : Res Int := Term.getIntValue i
example : Env (BitVec 8) := Term.getBitVecValue bv

/-- info: @Term.extractValue : [inst : Ω] → {α : Type} → [A : TermToValue α] → Term α → Env α -/
#guard_msgs in #check @Cvc.Typed.Term.extractValue

/-- info: @Term.getBitVecValue : [inst : Ω] → {size : Nat} → Term (BitVec size) → Env (BitVec size) -/
#guard_msgs in #check @Cvc.Typed.Term.getBitVecValue

end discipline



/-! ## Containers

As in the sort-erased layer, a sequence or a set reads back only from a model, while a bag and a
total map read back from the term itself.
-/

/-- Round-trips a value through a model, at the sort its Lean type denotes. -/
def roundTrip [Ω] (α : Type) [SrtLike α] (value : α) : Env α := do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst α "x"
  (do Term.equal x (← Term.mkValue value)) >>= s.assert
  s.checkSat (ifSat := s.getValue x)

/-- info:
Array  : #[1, 2, 3]
empty  : #[]
Set    : { 1, 2, 3 }
nested : #[#[1, 2], #[3]]
-/
#guard_msgs in #eval Env.runIO do
  println! "Array  : {← roundTrip (Array Int) #[1, 2, 3]}"
  println! "empty  : {← roundTrip (Array Int) #[]}"
  println! "Set    : {← roundTrip (Cvc.Set Int) (Cvc.Set.ofArray #[1, 2, 3])}"
  println! "nested : {← roundTrip (Array (Array Int)) #[#[1, 2], #[3]]}"

/-- info:
Bag      : { 1 ↦ 2, 3 ↦ 1 }
TotalMap : { 1 ↦ 10, 2 ↦ 20, _ ↦ 0 }
-/
#guard_msgs in #eval Env.runIO do
  let bag : Cvc.Bag Int := (Cvc.Bag.empty.insert 1 2).insert 3 1
  println! "Bag      : {← Term.extractValue (← Term.mkValue bag)}"

  let map : Cvc.TotalMap Int Int := ((Cvc.TotalMap.mkConst 0).insert 1 10).insert 2 20
  println! "TotalMap : {← Term.extractValue (← Term.mkValue map)}"



/-! ## Reading a model

`Solver.getValue` converts through the index, so a declared symbol comes back as the Lean value its
type denotes with nothing said at the call site.
-/

/-- info:
x  : 3
b  : true
xs : #[3, 4]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← s.declareConst Int "x"
  (do Term.equal x (← Term.mkValue (3 : Int))) >>= s.assert

  let b ← s.declareConst Bool "b"
  s.assert b

  let xs ← s.declareConst (Array Int) "xs"
  (do Term.equal xs (← Term.mkValue #[(3 : Int), 4])) >>= s.assert

  s.checkSat (ifSat := do
    println! "x  : {← s.getValue x}"
    println! "b  : {← s.getValue b}"
    println! "xs : {← s.getValue xs}")



/-! ## Classifying a value

Every reader has a predicate saying whether it will answer. Here the index already says *which*
reader applies, so a predicate takes only the terms it could ever be true of — `isInt32Value` on a
`Term Rat` is not a false answer, it does not typecheck.
-/

/-- info:
int32/64 : true / true
uint32   : true / false
sign     : 1 / -1
real32   : true → (3, 4)
algebraic: false
-/
#guard_msgs in #eval Env.runIO do
  let i ← Term.mkInt 42
  println! "int32/64 : {i.isInt32Value} / {i.isInt64Value}"
  let neg ← Term.mkInt (-7)
  println! "uint32   : {i.isUInt32Value} / {neg.isUInt32Value}"
  println! "sign     : {← i.getSign} / {← neg.getSign}"

  let r ← Term.mkReal (3/4 : Rat)
  println! "real32   : {r.isReal32Value} → {← r.getReal32Value}"
  println! "algebraic: {r.isRealAlgebraicNumber}"

/-- info:
bitvec : true
field  : true → -2
mode   : true → Cvc.Float.RoundingMode.towardZero
+oo    : true, posInf true, nan false
-/
#guard_msgs in #eval Env.runIO do
  println! "bitvec : {(← Term.mkValue (10 : BitVec 8)).isBitVecValue}"

  let ff ← Term.mkValueAs (Cvc.FiniteField 5) {repr := 3}
  println! "field  : {ff.isFiniteFieldValue} → {← ff.getFiniteFieldRepr}"

  let rm ← Term.mkRoundingMode .towardZero
  println! "mode   : {rm.isRoundingModeValue} → {← rm.getRoundingModeValue}"

  let posInf ← Term.mkValueAs (Cvc.Float 8 24) .posInf
  println! "+oo    : {posInf.isFloatValue}, posInf {posInf.isFloatPosInf}, nan {posInf.isFloatNaN}"

-- the index is what rules a wrong question out
section discipline
variable [Ω] (i : Term Int) (r : Term Rat) (bv : Term (BitVec 8))
  (rm : Term Cvc.Float.RoundingMode) (f : Term (Cvc.Float 8 24))

example : Bool := i.isInt32Value
example : Res Int32 := i.getInt32Value
example : Bool := r.isReal64Value
example : Bool := bv.isBitVecValue
example : Res Cvc.Float.RoundingMode := rm.getRoundingModeValue
example : Bool := f.isFloatNaN

/-- info: @Term.isInt32Value : [inst : Ω] → Term Int → Bool -/
#guard_msgs in #check @Cvc.Typed.Term.isInt32Value

/-- info: @Term.getSign : [inst : Ω] → {α : Type} → [inst_1 : ToTyp α] → [IsArith α] → Term α → Res Int -/
#guard_msgs in #check @Cvc.Typed.Term.getSign

end discipline



/-! ## Reading a term's own structure

Sub-terms are sort-erased: a term's index says nothing about its children's.
-/

/-- info:
sort   : Int
kind   : ADD
kids   : 2
symbol : x
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbol (α := Int) "x"
  let sum ← Term.add x (← Term.mkValue (1 : Int))

  println! "sort   : {← sum.getSort}"
  println! "kind   : {← sum.getKind}"
  println! "kids   : {sum.getKids.size}"
  println! "symbol : {← x.getSymbol}"

/-- info: @Term.getKids : [inst : Ω] → {α : Type} → Term α → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Term.getKids
