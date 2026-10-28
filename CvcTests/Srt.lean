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
(Int → Bool) → Real    → (-> (-> Int Bool) Real)        ✓
Set (Int → Bool)       → (Set (-> Int Bool))            ✓
Set ?                  → (Set ?)                        ✓
Bag ?                  → (Bag ?)                        ✓
Seq ?                  → (Seq ?)                        ✓
Array ? ?              → (Array ? ?)                    ✓
Set (Abstract BitVec _) → (Set ?BITVECTOR_TYPE)          ✓
Seq (Abstract _ → _)   → (Seq ?->)                      ✓
Array Int ?            → (Array Int ?)                  ✓
Array ? Int            → (Array ? Int)                  ✓
Int → ?                → (-> Int ?)                     ✓
Int → Abstract BitVec _ → (-> Int ?BITVECTOR_TYPE)       ✓
-/
#guard_msgs in #eval Env.runIO do
  let cases : List Typ := [
    .bool, .int, .real, .string, .regex, .roundingMode,
    .bitVec 8, .float 8 24, .finiteField 5,
    .arrayTo .int .bool, .set .int, .bag .int, .seq .int, .nullable .int,
    .prod [.int, .bool, .string], .prod [.int, .prod [.bool, .string]],
    .function .int (.function .bool .real), .function (.function .int .bool) .real,
    .set (.function .int .bool),
    -- the abstract sorts, which live in `Typ?` and so only occur where cvc5 accepts them
    .set .any, .bag .any, .seq .any, .arrayTo .any .any,
    .set (.abstract .bitVec), .seq (.abstract .function),
    -- and the mixed sorts, which had no spelling before the split
    .arrayTo .int .any, .arrayTo .any .int, .function .int .any,
    .function .int (.abstract .bitVec),
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
  let mk ← Cvc.Datatype.Ctor.Decl.mk "mk"
  let mk ← mk.addSelector "fst" (← Srt.int)
  let decl ← Cvc.Datatype.Decl.mk "Pair"
  let pair ← Srt.datatype (← decl.addCtor mk)
  let loc ← Srt.uninterpreted "Loc"

  let pairTyp ← pair.toTyp
  let locTyp ← loc.toTyp
  println! "datatype      : {pair} → {pairTyp} \
{if pairTyp == Typ.datatype "Pair" then "✓" else "✗"}"
  println! "uninterpreted : {loc} → {locTyp} \
{if locTyp == Typ.uninterpreted "Loc" then "✓" else "✗"}"

/-! An abstract sort has a `Typ?` but no `Typ`, that being cvc5's first-class rule: `toTyp?`
accepts one, `toTyp` refuses it. So the split is visible in which conversion answers. -/

/-- info:
?: toTyp? = ? | toTyp = `?` is an abstract sort, which cvc5 does not accept where a first-class one is wanted; it has a `Typ?` but no `Typ`
?BITVECTOR_TYPE: toTyp? = Abstract BitVec _ | toTyp = `?BITVECTOR_TYPE` is an abstract sort, which cvc5 does not accept where a first-class one is wanted; it has a `Typ?` but no `Typ`
-/
#guard_msgs in #eval Env.runIO do
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"
  for srt in [← Srt.any, ← Srt.abstract .bitVec] do
    println! "{srt}: toTyp? = {← srt.toTyp?} | toTyp = {← caught do pure s!"{← srt.toTyp}"}"

/-! What no `Typ` case describes at all is refused by both. -/

/-- info:
sort ctor    : `Typ` has no case for `U`, an uninterpreted sort constructor: it names a sort of arity greater than zero, which `Typ.uninterpreted` cannot describe
instantiated : `Typ` has no case for `(U Int)`, an instantiated sort: `Typ.datatype` and `Typ.uninterpreted` carry a name and nothing else
-/
#guard_msgs in #eval Env.runIO do
  let caught (code : Env Typ) : Env String := try pure s!"{← code}" catch e => pure s!"{e}"
  let ctor ← Srt.uninterpretedConstructor 1 "U"
  println! "sort ctor    : {← caught ctor.toTyp}"
  println! "instantiated : {← caught do (← ctor.instantiate #[← Srt.int]).toTyp}"



/-! ## Records

Structural, unlike a datatype: cvc5 builds the same sort from the same fields, so `toSrt` rebuilds
one rather than looking it up. **The order is part of the sort** — `{a : Int, b : Bool}` and
`{b : Bool, a : Int}` are different — which is why `Typ.record` takes a list and not a map.

Fields are `Typ`s, cvc5 refusing a field that is not first-class; a field may still *contain* an
abstract sort deeper down, as `{s : Set ?}` does.
-/

/-- info:
{a : Int}  →  __cvc5_record_a_Int  ✓
{a : Int, b : Bool}  →  __cvc5_record_a_Int_b_Bool  ✓
{b : Bool, a : Int}  →  __cvc5_record_b_Bool_a_Int  ✓
{r : {a : Int}}  →  __cvc5_record_r___cvc5_record_a_Int  ✓
{s : Set ?}  →  |__cvc5_record_s_(Set ?)|  ✓
Set ({a : Int})  →  (Set __cvc5_record_a_Int)  ✓
field order matters : true
-/
#guard_msgs in #eval Env.runIO do
  let cases : List Typ := [
    .record [("a", .int)],
    .record [("a", .int), ("b", .bool)],
    .record [("b", .bool), ("a", .int)],
    .record [("r", .record [("a", .int)])],
    .record [("s", .set .any)],
    .set (.record [("a", .int)]),
  ]
  for typ in cases do
    let srt ← typ.toSrt
    let back ← srt.toTyp
    println! "{typ}  →  {srt}  {if back == typ then "✓" else s!"✗ came back as {back}"}"

  let r₁ ← (Typ.record [("a", .int), ("b", .bool)]).toSrt
  let r₂ ← (Typ.record [("b", .bool), ("a", .int)]).toSrt
  println! "field order matters : {r₁ != r₂}"

/-! Distinct field names are **our** check, not cvc5's: it accepts `{a : Int, a : Bool}` and builds
a datatype with two selectors named `a`, which nothing can then select unambiguously. The check
sits on `Srt.record`, so both paths to a record sort get it. -/

/-- info:
via Srt.record : record sort has more than one field named `a`
via Typ.toSrt  : record sort has more than one field named `a`
-/
#guard_msgs in #eval Env.runIO do
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"
  println! "via Srt.record : {← caught do
    pure s!"{← Srt.record #[("a", ← Srt.int), ("a", ← Srt.bool)]}"}"
  println! "via Typ.toSrt  : {← caught do
    pure s!"{← (Typ.record [("a", .int), ("a", .bool)]).toSrt}"}"



/-! ## `Record`, the index a record sort is named by

`Record fields` is the Lean type that denotes a record sort. Since the sort is *structural*, the
index is canonical in both directions: `ToTyp` maps it to a `Typ.record`, and `Srt.toTyp` maps a
record sort back to exactly the field list that names it.
-/

/-- info:
{a : Int, b : Bool}  →  __cvc5_record_a_Int_b_Bool
round trip  : true
nested      : __cvc5_record_r___cvc5_record_a_Int
in a set    : (Set __cvc5_record_a_Int)
in an array : (Array Int __cvc5_record_a_Int)
of a set    : |__cvc5_record_s_(Set Int)|
-/
#guard_msgs in #eval Env.runIO do
  let srt ← Srt.of (Record [("a", Int), ("b", Bool)])
  println! "{← srt.toTyp}  →  {srt}"
  println! "round trip  : {(← srt.toTyp) == Typ.record [("a", .int), ("b", .bool)]}"
  println! "nested      : {← Srt.of (Record [("r", Record [("a", Int)])])}"
  println! "in a set    : {← Srt.of (Set (Record [("a", Int)]))}"
  println! "in an array : {← Srt.of (TotalMap Int (Record [("a", Int)]))}"
  println! "of a set    : {← Srt.of (Record [("s", Set Int)])}"

/-! Neither uniqueness of field names nor non-emptiness is something the index can state; both are
`Srt.record`'s checks, and that is where they are caught. An empty record denotes what the empty
tuple already denotes, so it is refused rather than left as a second spelling of it. -/

/-- info:
duplicate : record sort has more than one field named `a`
empty     : a record sort must have at least one field
via Typ   : a record sort must have at least one field
-/
#guard_msgs in #eval Env.runIO do
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"
  println! "duplicate : {← caught do pure s!"{← Srt.of (Record [("a", Int), ("a", Bool)])}"}"
  println! "empty     : {← caught do pure s!"{← Srt.of (Record [])}"}"
  println! "via Typ   : {← caught do pure s!"{← (Typ.record []).toSrt}"}"

/-! ### `FieldOf` resolves a name to its type

This is what lets a typed field access be written as a name and still answer a term at the field's
own type: the class walks the list and the head match wins.
-/

/-- The type `FieldOf` answers for a field, so that *inference* is pinned rather than checking. -/
abbrev fieldType (fields : List (String × Type)) (name : String) {gamma : Type}
  [FieldOf fields name gamma] : Type := gamma

example : fieldType [("a", Int), ("b", Bool)] "a" = Int := rfl
example : fieldType [("a", Int), ("b", Bool)] "b" = Bool := rfl
example : fieldType [("r", Record [("a", Int)])] "r" = Record [("a", Int)] := rfl

/-- A duplicated name resolves to the first, matching what `Srt.record` reports — though such an
index has no sort at all. -/
example : fieldType [("a", Int), ("a", Bool)] "a" = Int := rfl

/-! A name that is not a field has no instance, so it does not compile — and neither does a field
asked for at the wrong type. These are stated at an explicit type rather than through `fieldType`,
so that the message names the field list instead of a metavariable. -/

/--
error: failed to synthesize instance of type class
  FieldOf [("a", Int), ("b", Bool)] "c" Int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : FieldOf [("a", Int), ("b", Bool)] "c" Int := inferInstance

/--
error: failed to synthesize instance of type class
  FieldOf [("a", Int), ("b", Bool)] "a" Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : FieldOf [("a", Int), ("b", Bool)] "a" Bool := inferInstance

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
