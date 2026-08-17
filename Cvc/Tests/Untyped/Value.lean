/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped

public meta import Cvc.Untyped



/-! # Values, sort-erased

A value round-trips: `mkValue` builds the term denoting it, `getValue` reads it back. These check
the round trip for every type an instance exists for, and then that a *model* value — which is
what the classes are really for — comes back as the Lean value it denotes.
-/
namespace Cvc.Tests.Untyped.Value

open Cvc
open Cvc.Untyped



/-! ## Scalars round-trip -/

/-- info:
Bool   : true
Int    : -7
Rat    : -3/4
String : hello world
BitVec : 0x0a#8
-/
#guard_msgs in #eval Env.runIO do
  println! "Bool   : {← Term.getValueAs Bool (← Term.mkValue true)}"
  println! "Int    : {← Term.getValueAs Int (← Term.mkValue (-7 : Int))}"
  println! "Rat    : {← Term.getValueAs Rat (← Term.mkValue (-3/4 : Rat))}"
  println! "String : {← Term.getValueAs String (← Term.mkValue "hello world")}"
  println! "BitVec : {← Term.getValueAs (BitVec 8) (← Term.mkValue (10 : BitVec 8))}"

-- `Nat` builds a term but has no reader: the sort is `Int`, so reading one back would have to fail
-- on a negative value rather than answer
/-- info: Nat as Int : 42 -/
#guard_msgs in #eval Env.runIO do
  println! "Nat as Int : {← Term.getValueAs Int (← Term.mkValueAs Nat 42)}"

-- a bit-vector is read at the size asked for, and a mismatch is an error rather than a truncation
/-- info: wrong size : caught -/
#guard_msgs in #eval Env.runIO do
  let term ← Term.mkValue (10 : BitVec 8)
  let outcome ←
    try
      let _ ← Term.getValueAs (BitVec 16) term
      pure "no error"
    catch _ => pure "caught"
  println! "wrong size : {outcome}"



/-! ## Containers round-trip through a model

A container value is a *spine* of applications, and only some of those spines are constants cvc5
will read back. `seq.++` of unit sequences is a term denoting a sequence, but it is not a sequence
*value*, and neither is a union of singleton bags a bag value — the accessors want the normal forms
a model produces. So the round trip for these goes through the solver: build the term, constrain a
symbol to equal it, and read the symbol back out of the model.

A bag and a total map are the exceptions: reading those back walks the term's own kind and
children, so a built spine works directly — which is just as well for the total map, since
asserting a `STORE_ALL` needs cvc5's `--arrays-exp`.
-/

/-- Round-trips a value through a model, at whatever sort `α` denotes. -/
def roundTrip [Ω] (α : Type) [SrtLike α] (value : α) : Env α := do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst "x" (← Srt.of α)
  (do Term.equal x (← Term.mkValue value)) >>= s.assert
  s.checkSat (ifSat := s.getValueAs α x)

/-- info:
Array : #[1, 2, 3]
Set   : { 1, 2, 3 }
-/
#guard_msgs in #eval Env.runIO do
  println! "Array : {← roundTrip (Array Int) #[1, 2, 3]}"
  println! "Set   : {← roundTrip (Cvc.Set Int) (Cvc.Set.ofArray #[1, 2, 3])}"

-- the empty container is the base case of each spine
/-- info:
Array : #[]
Set   : ∅
-/
#guard_msgs in #eval Env.runIO do
  println! "Array : {← roundTrip (Array Int) #[]}"
  println! "Set   : {← roundTrip (Cvc.Set Int) Cvc.Set.empty}"

-- nesting works because the instances are recursive
/-- info: nested : #[#[1, 2], #[3]] -/
#guard_msgs in #eval Env.runIO do
  println! "nested : {← roundTrip (Array (Array Int)) #[#[1, 2], #[3]]}"

-- a bag and a total map read back from the term itself, no solver involved
/-- info:
Bag      : { 1 ↦ 2, 3 ↦ 1 }
empty bag: ∅
TotalMap : { 1 ↦ 10, 2 ↦ 20, _ ↦ 0 }
-/
#guard_msgs in #eval Env.runIO do
  let bag : Cvc.Bag Int := (Cvc.Bag.empty.insert 1 2).insert 3 1
  println! "Bag      : {← Term.getValueAs (Cvc.Bag Int) (← Term.mkValue bag)}"
  let empty : Cvc.Bag Int := Cvc.Bag.empty
  println! "empty bag: {← Term.getValueAs (Cvc.Bag Int) (← Term.mkValue empty)}"

  let map : Cvc.TotalMap Int Int := ((Cvc.TotalMap.mkConst 0).insert 1 10).insert 2 20
  println! "TotalMap : {← Term.getValueAs (Cvc.TotalMap Int Int) (← Term.mkValue map)}"



/-! ## Floats and finite fields

A floating-point value is one of the five distinguished constants or a bit pattern, and its sizes
come off the sort rather than the term. A finite-field element likewise recovers its size from the
sort, and reading one at the wrong size is an error.

`Cvc.Float exp sig` follows SMT-LIB: `sig` counts the hidden bit, so the pattern is
`exp + sig` wide. Single precision is `Float 8 24` at 32 bits, and cvc5 canonicalises even `+oo`
into a pattern — which is why the round trip below exercises the constants at all.
-/

/-- info:
+oo      : Float[8, 24, 0x7f800000#32]
NaN      : Float[8, 24, 0x7fc00000#32]
-0       : Float[8, 24, 0x80000000#32]
pi       : Float[8, 24, 0x40490fdb#32]
wrong exp: caught
-/
#guard_msgs in #eval Env.runIO do
  let roundTrip (f : Cvc.Float 8 24) : Env (Cvc.Float 8 24) := do
    Term.getValueAs (Cvc.Float 8 24) (← Term.mkValue f)
  println! "+oo      : {← roundTrip .posInf}"
  println! "NaN      : {← roundTrip .nan}"
  println! "-0       : {← roundTrip .negZero}"
  println! "pi       : {← roundTrip (.ofBitVec 0x40490fdb)}"

  let outcome ←
    try
      let single ← Term.mkValueAs (Cvc.Float 8 24) .posInf
      let _ ← Term.getValueAs (Cvc.Float 11 53) single
      pure "no error"
    catch _ => pure "caught"
  println! "wrong exp: {outcome}"

-- a field element comes back in cvc5's symmetric representation, so `3` in GF(5) reads as `-2`
/-- info:
field      : -2
wrong size : caught
-/
#guard_msgs in #eval Env.runIO do
  let elem : Cvc.FiniteField 5 := {repr := 3}
  let term ← Term.mkValue elem
  println! "field      : {← Term.getValueAs (Cvc.FiniteField 5) term}"

  let outcome ←
    try
      let _ ← Term.getValueAs (Cvc.FiniteField 7) term
      pure "no error"
    catch _ => pure "caught"
  println! "wrong size : {outcome}"



/-! ## Reading a model

This is what the classes are for: a solver answers with terms, and an instance turns one into the
Lean value it denotes.
-/

/-- info:
x        : 3
xs       : #[3, 4]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let int ← Srt.int
  let x ← s.declareConst "x" int
  (do Term.equal x (← Term.mkValue (3 : Int))) >>= s.assert

  let xs ← s.declareConst "xs" (← Srt.of (Array Int))
  (do Term.equal xs (← Term.mkValue #[(3 : Int), 4])) >>= s.assert

  s.checkSat (ifSat := do
    println! "x        : {← s.getValueAs Int x}"
    println! "xs       : {← s.getValueAs (Array Int) xs}")



/-! ## Classifying a value

Every reader has a predicate saying whether it will answer. The machine-width ones are views of an
integer or real value rather than distinct representations, so they say whether a value *fits*.
-/

/-- info:
int      : true
int32/64 : true / true
uint32   : true
neg uint : false
sign     : 1 / -1 / 0
real32   : true → (3, 4)
algebraic: false
-/
#guard_msgs in #eval Env.runIO do
  let i ← Term.mkInt 42
  println! "int      : {i.isIntValue}"
  println! "int32/64 : {i.isInt32Value} / {i.isInt64Value}"
  println! "uint32   : {i.isUInt32Value}"

  -- a negative integer does not fit an unsigned view
  let neg ← Term.mkInt (-7)
  println! "neg uint : {neg.isUInt32Value}"

  println! "sign     : {← i.getSign} / {← neg.getSign} / {← (← Term.mkInt 0).getSign}"

  let r ← Term.mkReal (3/4 : Rat)
  println! "real32   : {r.isReal32Value} → {← r.getReal32Value}"
  -- a rational is not an algebraic number in cvc5's sense
  println! "algebraic: {r.isRealAlgebraicNumber}"

/-- info:
32-bit   : 42 / 42
64-bit   : 42 / 42
-/
#guard_msgs in #eval Env.runIO do
  let i ← Term.mkInt 42
  println! "32-bit   : {← i.getInt32Value} / {← i.getUInt32Value}"
  println! "64-bit   : {← i.getInt64Value} / {← i.getUInt64Value}"

-- `isSetValue` says *value*, not "set-sorted": a built insert spine is a set-sorted term but not a
-- canonical constant, which is the same reason `getSetValue` only works on a model's answer
/-- info:
bitvec   : true
built set: false
seq      : true
const arr: true
field    : true → -2
-/
#guard_msgs in #eval Env.runIO do
  println! "bitvec   : {(← Term.mkValue (10 : BitVec 8)).isBitVecValue}"
  println! "built set: {(← Term.mkValue (Cvc.Set.ofArray #[(1 : Int)])).isSetValue}"
  println! "seq      : {(← Term.mkValueAs (Array Int) #[]).isSeqValue}"
  let arr ← Term.mkConstArray (← Srt.of (Cvc.TotalMap Int Int)) (← Term.mkInt 0)
  println! "const arr: {arr.isConstArray}"
  let ff ← Term.mkValueAs (Cvc.FiniteField 5) {repr := 3}
  println! "field    : {ff.isFiniteFieldValue} → {← ff.getFiniteFieldRepr}"



/-! ## Rounding modes and float patterns

A rounding mode round-trips: cvc5 exposes the accessor, so this is a real conversion rather than a
stub. A floating-point constant is always a bit pattern, and the five predicates classify it.
-/

/-- info:
mode     : true → Cvc.Float.RoundingMode.towardZero
float    : true
+oo      : posInf true, nan false, negZero false
NaN      : posInf false, nan true
sizes    : 8 / 24
-/
#guard_msgs in #eval Env.runIO do
  let rm ← Term.mkRoundingMode .towardZero
  println! "mode     : {rm.isRoundingModeValue} → {← rm.getRoundingModeValue}"

  let posInf ← Term.mkValueAs (Cvc.Float 8 24) .posInf
  println! "float    : {posInf.isFloatValue}"
  println! "+oo      : posInf {posInf.isFloatPosInf}, nan {posInf.isFloatNaN}, \
negZero {posInf.isFloatNegZero}"

  let nan ← Term.mkValueAs (Cvc.Float 8 24) .nan
  println! "NaN      : posInf {nan.isFloatPosInf}, nan {nan.isFloatNaN}"

  let (exp, sig, _) ← posInf.getFloatComponents
  println! "sizes    : {exp} / {sig}"



/-! ## Reading a term's own structure -/

/-- info:
sort     : Int
kind     : ADD
kids     : 2
symbol   : x, true
no symbol: false
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let sum ← Term.add x (← Term.mkValue (1 : Int))

  println! "sort     : {← sum.getSort}"
  println! "kind     : {← sum.getKind}"
  println! "kids     : {sum.getKids.size}"
  println! "symbol   : {← x.getSymbol}, {← x.hasSymbol}"
  println! "no symbol: {← sum.hasSymbol}"

-- identity: distinct terms get distinct ids
/-- info: distinct ids : true -/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkInt 1
  let y ← Term.mkInt 2
  println! "distinct ids : {(← x.getId) != (← y.getId)}"

/-- info: sized kids : caught -/
#guard_msgs in #eval Env.runIO do
  let sum ← Term.add (← Term.mkValue (1 : Int)) (← Term.mkValue (2 : Int))
  let outcome ←
    try
      let _ ← sum.getSizedKids 3
      pure "no error"
    catch _ => pure "caught"
  println! "sized kids : {outcome}"
