/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Srt
import Cvc.Types
-- for the datatype builders, so that a declared sort has something to round-trip
import Cvc.Untyped.Theory.Datatype

public meta import Cvc.Srt
public meta import Cvc.Types
public meta import Cvc.Untyped.Theory.Datatype



/-! # Sorts

`Srt` is layer-neutral, so there is one test module rather than one per layer.
-/
namespace Cvc.Tests.Srt

open Cvc
open Cvc



/-! ## Constructors -/

/-- info:
bool     : Bool
int      : Int
real     : Real
string   : String
regex    : RegLan
mode     : RoundingMode
bitVec   : (_ BitVec 8)
float    : (_ FloatingPoint 8 24)
field    : (_ FiniteField 5)
array    : (Array Int Bool)
set      : (Set Int)
bag      : (Bag Int)
seq      : (Seq Int)
tuple    : (Tuple Int Bool)
function : (-> Int Bool Real)
-/
#guard_msgs in #eval Env.runIO do
  println! "bool     : {← Srt.bool}"
  println! "int      : {← Srt.int}"
  println! "real     : {← Srt.real}"
  println! "string   : {← Srt.string}"
  println! "regex    : {← Srt.regex}"
  println! "mode     : {← Srt.roundingMode}"
  println! "bitVec   : {← Srt.bitVec 8}"
  println! "float    : {← Srt.float 8 24}"
  println! "field    : {← Srt.finiteField 5}"
  println! "array    : {← Srt.arrayTo (← Srt.int) (← Srt.bool)}"
  println! "set      : {← Srt.set (← Srt.int)}"
  println! "bag      : {← Srt.bag (← Srt.int)}"
  println! "seq      : {← Srt.seq (← Srt.int)}"
  println! "tuple    : {← Srt.tuple #[← Srt.int, ← Srt.bool]}"
  println! "function : {← Srt.function #[← Srt.int, ← Srt.bool] (← Srt.real)}"

-- the sorts that have no Lean index yet, so no `Srt.of` reaches them
/-- info:
predicate: (-> Int Bool Bool)
nullable : (Nullable Int)
record   : __cvc5_record_a_Int_b_Bool
param    : X
uninterp : U
ctor     : U2
unresolvd: L
field/str: (_ FiniteField 13)
-/
#guard_msgs in #eval Env.runIO do
  println! "predicate: {← Srt.predicate #[← Srt.int, ← Srt.bool]}"
  println! "nullable : {← Srt.nullable (← Srt.int)}"
  println! "record   : {← Srt.record #[("a", ← Srt.int), ("b", ← Srt.bool)]}"
  println! "param    : {← Srt.param "X"}"
  println! "uninterp : {← Srt.uninterpreted "U"}"
  println! "ctor     : {← Srt.uninterpretedConstructor 2 "U2"}"
  println! "unresolvd: {← Srt.unresolvedDatatype "L"}"
  println! "field/str: {← Srt.finiteFieldOfString "d" (base := 16)}"



/-! ## Testers

Which family a sort belongs to. Each guards the accessors of that family.
-/

/-- info:
int      : isInt true, isReal false, isBitVec false
bitVec   : isBitVec true, isInt false
array    : isArray true, isSet false
set      : isSet true, isBag false
seq      : isSeq true, isSet false
tuple    : isTuple true, isDatatype true
function : isFunction true, isPredicate false
predicate: isFunction true, isPredicate true
uninterp : isUninterpretedSort true
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  println! "int      : isInt {int.isInt}, isReal {int.isReal}, isBitVec {int.isBitVec}"
  let bv ← Srt.bitVec 8
  println! "bitVec   : isBitVec {bv.isBitVec}, isInt {bv.isInt}"
  let arr ← Srt.arrayTo int (← Srt.bool)
  println! "array    : isArray {arr.isArray}, isSet {arr.isSet}"
  let set ← Srt.set int
  println! "set      : isSet {set.isSet}, isBag {set.isBag}"
  let seq ← Srt.seq int
  println! "seq      : isSeq {seq.isSeq}, isSet {seq.isSet}"
  -- a tuple *is* a datatype, which is how its components are reached
  let tup ← Srt.tuple #[int, ← Srt.bool]
  println! "tuple    : isTuple {tup.isTuple}, isDatatype {tup.isDatatype}"
  let fn ← Srt.function #[int] (← Srt.real)
  println! "function : isFunction {fn.isFunction}, isPredicate {fn.isPredicate}"
  -- a predicate is a function into `Bool`, so it is both
  let pred ← Srt.predicate #[int]
  println! "predicate: isFunction {pred.isFunction}, isPredicate {pred.isPredicate}"
  let u ← Srt.uninterpreted "U"
  println! "uninterp : isUninterpretedSort {u.isUninterpreted}"



/-! ## Accessors

Each comes in two forms: the plain one fails outside its family, the `?`-suffixed one answers
`none`. Asking a bit-vector for an array's index sort is the whole point of having both.
-/

/-- info:
bitVec size : 8
float sizes : 8 / 24
field size  : 5
array       : Int / Bool
set elem    : Int
bag elem    : Int
seq elem    : Int
nullable    : Int
tuple       : 2 / #[Int, Bool]
function    : 2 / #[Int, Bool] / Real
kind        : ARRAY_SORT
symbol      : true / U
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  println! "bitVec size : {← (← Srt.bitVec 8).getBitVecSize}"
  let flt ← Srt.float 8 24
  println! "float sizes : {← flt.getFloatExponentSize} / {← flt.getFloatSignificandSize}"
  println! "field size  : {← (← Srt.finiteField 5).getFiniteFieldSize}"

  let arr ← Srt.arrayTo int (← Srt.bool)
  println! "array       : {← arr.getArrayIndexSort} / {← arr.getArrayElementSort}"
  println! "set elem    : {← (← Srt.set int).getSetElementSort}"
  println! "bag elem    : {← (← Srt.bag int).getBagElementSort}"
  println! "seq elem    : {← (← Srt.seq int).getSeqElementSort}"
  println! "nullable    : {← (← Srt.nullable int).getNullableElementSort}"

  let tup ← Srt.tuple #[int, ← Srt.bool]
  println! "tuple       : {← tup.getTupleLength} / {(← tup.getTupleSorts).map toString}"

  let fn ← Srt.function #[int, ← Srt.bool] (← Srt.real)
  println! "function    : {← fn.getFunctionArity} / \
{(← fn.getFunctionDomainSorts).map toString} / {← fn.getFunctionCodomainSort}"

  println! "kind        : {← arr.getKind}"
  let u ← Srt.uninterpreted "U"
  println! "symbol      : {← u.hasSymbol} / {← u.getSymbol}"

-- the `?` form is what a tester is for: ask, or check first
/-- info:
wrong family : none
right family : (some Int)
caught       : true
-/
#guard_msgs in #eval Env.runIO do
  let bv ← Srt.bitVec 8
  println! "wrong family : {bv.getArrayIndexSort?}"
  let arr ← Srt.arrayTo (← Srt.int) (← Srt.bool)
  println! "right family : {arr.getArrayIndexSort?}"

  let outcome ←
    try
      let _ ← bv.getArrayIndexSort
      pure false
    catch _ => pure true
  println! "caught       : {outcome}"



/-! ## Instantiation and substitution -/

/-- info:
uninterpreted ctor arity : 1
instantiated             : (U Int)
is instantiated          : true
parameters               : #[Int]
constructor              : U
substituted              : (Array Real Bool)
-/
#guard_msgs in #eval Env.runIO do
  let ctor ← Srt.uninterpretedConstructor 1 "U"
  println! "uninterpreted ctor arity : {← ctor.getUninterpretedSortConstructorArity}"

  let inst ← ctor.instantiate #[← Srt.int]
  println! "instantiated             : {inst}"
  println! "is instantiated          : {inst.isInstantiated}"
  println! "parameters               : {(← inst.getInstantiatedParameters).map toString}"
  println! "constructor              : {← inst.getUninterpretedSortConstructor}"

  let int ← Srt.int
  let arr ← Srt.arrayTo int (← Srt.bool)
  println! "substituted              : {← arr.substitute #[int] #[← Srt.real]}"



/-! ## `Typ` ↔ `Srt`

`Typ.toSrt` builds a sort from the pure Lean description; `Srt.toTyp` reads one back. Every case
`Typ` has round-trips, which is what these check — the sort each produces is pinned too, since the
two conversions agreeing on a *wrong* sort would otherwise go unnoticed.

Two cases are rebuilt rather than read off, both because `toSrt` flattens them:

- a **function**'s domain is n-ary in cvc5 and curried in `Typ`, so `toTyp` folds the spine back to
  the right. This is stable because a cvc5 codomain is never itself a function sort: `α → β → γ`
  *is* `(-> α β γ)`, and `(α → β) → γ` is the different sort `(-> (-> α β) γ)`, where the nesting
  sits in the domain;
- a **tuple**'s components are flat on both sides, so they come back as they went.
-/

/-- info:
Bool                   → Bool                           ✓
Int                    → Int                            ✓
Real                   → Real                           ✓
String                 → String                         ✓
Regex                  → RegLan                         ✓
RoundingMode           → RoundingMode                   ✓
BitVec 8               → (_ BitVec 8)                   ✓
Float 8 24             → (_ FloatingPoint 8 24)         ✓
FiniteField 5          → (_ FiniteField 5)              ✓
Array Int Bool         → (Array Int Bool)               ✓
Set Int                → (Set Int)                      ✓
Bag Int                → (Bag Int)                      ✓
Seq Int                → (Seq Int)                      ✓
Option Int             → (Nullable Int)                 ✓
Int × Bool × String    → (Tuple Int Bool String)        ✓
Int × (Bool × String)  → (Tuple Int (Tuple Bool String)) ✓
Int → Bool → Real      → (-> Int Bool Real)             ✓
Int → Bool → Real      → (-> (-> Int Bool) Real)        ✓
Set (Int → Bool)       → (Set (-> Int Bool))            ✓
Abstract BitVec _      → ?BITVECTOR_TYPE                ✓
Abstract Float _ _     → ?FLOATINGPOINT_TYPE            ✓
Abstract FiniteField _ → ?FINITE_FIELD_TYPE             ✓
Abstract _ → _         → ?->                            ✓
-/
#guard_msgs in #eval Env.runIO do
  let cases : List Typ := [
    .bool, .int, .real, .string, .regex, .roundingMode,
    .bitVec 8, .float 8 24, .finiteField 5,
    .arrayTo .int .bool, .set .int, .bag .int, .seq .int, .nullable .int,
    .prod [.int, .bool, .string], .prod [.int, .prod [.bool, .string]],
    .function .int (.function .bool .real), .function (.function .int .bool) .real,
    .set (.function .int .bool),
    .abstract .bitVec, .abstract .float, .abstract .finiteField, .abstract .function,
  ]
  let pad (s : String) (n : Nat) : String := s ++ "".pushn ' ' (n - s.length)
  for typ in cases do
    let srt ← typ.toSrt
    let back ← srt.toTyp
    let mark := if back == typ then "✓" else s!"✗ came back as {back}"
    println! "{pad (toString typ) 22} → {pad (toString srt) 30} {mark}"

/-! A *declared* sort round-trips through its name, and `toTyp` checks that name against the
scope's registry — a `Typ` naming a sort the registry does not hold, or holds under a different
sort, would not resolve back and is refused rather than answered. -/

/-- info:
datatype      : Pair → Pair ✓
uninterpreted : Loc → Uninterpreted `Loc` ✓
-/
#guard_msgs in #eval Env.runIO do
  let mk ← Cvc.Datatype.Constructor.Decl.mk "mk"
  let mk ← mk.addSelector "fst" (← Srt.int)
  let decl ← Cvc.Datatype.Decl.mk "Pair"
  let pair ← Srt.datatype (← decl.addConstructor mk)
  let loc ← Srt.uninterpreted "Loc"

  let pairTyp ← pair.toTyp
  let locTyp ← loc.toTyp
  println! "datatype      : {pair} → {pairTyp} \
{if pairTyp == Typ.datatype "Pair" then "✓" else "✗"}"
  println! "uninterpreted : {loc} → {locTyp} \
{if locTyp == Typ.uninterpreted "Loc" then "✓" else "✗"}"

/-! What no `Typ` case describes is refused, rather than approximated.

The **abstract container** sorts are the surprising entry: cvc5 keeps only a bit-vector, float,
finite-field or function abstraction as an abstract sort. An abstract array, bag, set or sequence
becomes that container over the fully abstract sort `?` — `Srt.abstract .set` *is* `(Set ?)`, of
sort kind `SET_SORT` — and `Typ` has no case for `?`. So those four are the one place where
`Typ.toSrt` produces a sort `Srt.toTyp` cannot read back.
-/

/-- info:
abstract array : `Typ` has no case for `?`, the fully abstract sort
abstract set   : `Typ` has no case for `?`, the fully abstract sort
abstract bag   : `Typ` has no case for `?`, the fully abstract sort
abstract seq   : `Typ` has no case for `?`, the fully abstract sort
record         : `Typ` has no case for the record sort `__cvc5_record_fst_Int`
sort ctor      : `Typ` has no case for `U`, an uninterpreted sort constructor: it names a sort of arity greater than zero, which `Typ.uninterpreted` cannot describe
instantiated   : `Typ` has no case for `(U Int)`, an instantiated sort: `Typ.datatype` and `Typ.uninterpreted` carry a name and nothing else
-/
#guard_msgs in #eval Env.runIO do
  let caught (code : Env Typ) : Env String := try pure s!"{← code}" catch e => pure s!"{e}"
  for (name, a) in
    [("array ", Srt.Abstract.array), ("set   ", .set), ("bag   ", .bag), ("seq   ", .seq)]
  do
    println! "abstract {name}: {← caught do (← Srt.abstract a).toTyp}"

  println! "record         : {← caught do (← Srt.record #[("fst", ← Srt.int)]).toTyp}"
  let ctor ← Srt.uninterpretedConstructor 1 "U"
  println! "sort ctor      : {← caught ctor.toTyp}"
  println! "instantiated   : {← caught do (← ctor.instantiate #[← Srt.int]).toTyp}"



/-! ## `Kind`, `SortKind` and `Op` are re-exported

Three lean-cvc5 types are used raw rather than wrapped, and re-exported so that naming one does not
mean reaching into `cvc5`. Constructors come from dot notation on the expected type, as everywhere
else in Lean.
-/

section reexports
variable (k : Kind) (sk : SortKind) (o : Op)

example : Type := Kind
example : Type := SortKind
example : Type := Op

example : Kind := .ADD
example : SortKind := .ARRAY_SORT
example : Bool := k == .ADD
example : Bool := match sk with | .ARRAY_SORT | .SET_SORT => true | _ => false

-- `Op`'s own methods, by dot notation on a value
example : Kind := o.getKind
example : Bool := o.isIndexed
example : Nat := o.getNumIndices

end reexports
