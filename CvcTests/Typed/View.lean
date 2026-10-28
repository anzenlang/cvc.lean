/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Theory
public import Cvc.Typed.Core.Solver

public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Core.Solver



/-! # Typed views

Every theory's typed view is registered by importing the theory, and `def.term_view V`, under
`open Cvc.Typed`, gathers them into `V : Typ → Type`. Matching refines the sort: an operator whose
result sort is fixed only matches at that sort, and its kids come back at the sorts its signature
gives them.
-/
namespace Cvc.Tests.Typed.View

open Cvc
open Cvc.Typed

/-! ## The aggregate -/

public section variable [Ω]

def.term_view V

end

/-- info: @V.lt : [inst : Ω] → (α : Typ) → {h0 : α.isArith = true} → Kids α.Denote → V Typ.bool -/
#guard_msgs in #check @V.lt

/--
info: @V.add : [inst : Ω] → {τ : Typ} → {h0 : (Typ.of τ.Denote).isArith = true} → Kids τ.Denote → V τ
-/
#guard_msgs in #check @V.add

/--
info: @V.bvExtract : [inst : Ω] → {w : Nat} → (hi lo n : Nat) → {h0 : hi - lo + 1 = w} → Term (BitVec n) → V (Typ.bitVec w)
-/
#guard_msgs in #check @V.bvExtract

/-- info: @V.setEmpty : [inst : Ω] → {γ : Typ} → {ord : Ord γ.Denote} → V (Typ.set (Typ?.typ γ)) -/
#guard_msgs in #check @V.setEmpty

/-! The hand-written views: application, quantifiers, datatypes. An application's arguments and a
quantifier's variables are typed by a list of sorts, from which the function's index is computed. -/

/--
info: @V.apply : [inst : Ω] → {τ : Typ} → (doms : List Typ) → Term (Typ.arrows doms τ.Denote) → View.Apply.Args doms → V τ
-/
#guard_msgs in #check @V.apply

/--
info: @V.forall' : [inst : Ω] → (doms : List Typ) → View.Quant.Vars doms → Term Bool → Option Untyped.Term → V Typ.bool
-/
#guard_msgs in #check @V.forall'

/--
info: @V.construct : [inst : Ω] → {τ : Typ} → String → (doms : List Typ) → View.Datatype.Fields doms → V τ
-/
#guard_msgs in #check @V.construct

/-! ## Taking terms apart -/

section variable [Ω]

/-- One line per term: the operator, and what it holds.

The sort is matched alongside the view, so that each alternative refines it.
-/
def describe (τ : Typ) (t : Term τ.Denote) : Env String := do
  let v ← V.of τ t
  return match τ, v with
  | _, .value t => s!"a value: {t}"
  | _, .symbol name => s!"the symbol {name}"
  | _, .bvar x => s!"the bound variable {x.toTerm}"
  | .bool, .lt α ks => s!"a `<` over {α}, of {ks.val.size} operands"
  | _, .add ks => s!"a sum of {ks.val.size} terms"
  | .bitVec w, .bvExtract hi lo n bv => s!"bits {hi} to {lo} of the {n}-bit {bv}, so {w} bits"
  | _, .setEmpty => "the empty set"
  | _, .apply doms f _ => s!"{f} applied to arguments of sorts {doms}"
  | .bool, .forall' _ vars body _ => s!"∀ {vars.toStrings}, {body}"
  | _, .construct ctor _ args => s!"built by {ctor} from {args.toStrings}"
  | _, .other t => s!"something else: {t}"
  | _, _ => "an operator this test does not describe"

/-- A sum's summands, typed: at `.int`, the kids of `add` are `Term Int`s. -/
def summands (t : Term Int) : Env (Array (Term Int)) := do
  return match ← V.of .int t with
  | .add ks => ks.val
  | _ => #[]

end

/-- info: a value: 3
the symbol x
a `<` over Int, of 2 operands
a sum of 2 terms
bits 3 to 0 of the 8-bit b, so 4 bits
the empty set
f applied to arguments of sorts [Int, Bool]
∀ [n : Int], (< n x)
built by __cvc5_record_a_Int_ctor from [x]
an operator this test does not describe
summands: #[x, y]
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  let p ← Term.mkSymbolAs Bool "p"
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  let b ← Term.mkSymbolAs (BitVec 8) "b"
  let r : Term (Record [("a", Int)]) ← smt! {a := x}
  println! ← describe .int (← Term.mkInt 3)
  println! ← describe .int x
  println! ← describe .bool (← Term.lt x y)
  println! ← describe .int (← Term.add x y)
  println! ← describe (.bitVec 4) (← Term.bvExtract 3 0 b)
  println! ← describe (.set .int) (← Term.setEmpty (α := Int))
  println! ← describe .int (← Term.apply2 f x p)
  println! ← describe .bool (← Term.forallH (names := ["n"]) fun (n : Term Int) => Term.lt n x)
  println! ← describe (Typ.of (Record [("a", Int)])) r
  println! ← describe .bool (← Term.and p p)
  println! s!"summands: {← summands (← Term.add x y)}"

/-! ## Records, tuples and nullables

The datatype view takes them apart generically, by constructor name. When the index is known, these
give back their typed surface instead, and `none` for a term that is not a literal.
-/

/-- info: record: 7, true
not a literal: none
pair: 1, false
null: none
some: 5
-/
#guard_msgs in #eval Env.runIO do
  let r : Term (Record [("a", Int), ("b", Bool)]) ← smt! {a := 7, b := true}
  let some fs ← r.recordFields? | throwUser "not a record literal"
  println! "record: {fs.get "a"}, {fs.get "b"}"
  let s ← Term.mkSymbolAs (Record [("a", Int), ("b", Bool)]) "s"
  println! "not a literal: {(← s.recordFields?).map fun fs => toString (fs.get "a")}"
  let pair ← Term.mkTuple (← Term.mkInt 1) (.last (← Term.mkBool false))
  let some (a, b) ← pair.pairComponents? | throwUser "not a pair literal"
  println! "pair: {a}, {b}"
  let some none ← (← Term.mkNull' Int).nullableCases? | throwUser "not null"
  println! "null: none"
  let some (some v) ← (← Term.nullableSome (← Term.mkInt 5)).nullableCases?
    | throwUser "not some"
  println! "some: {v}"



/-! ## Matching at the wrong sort

The mismatch names the denoted types, `Rat` and `Set Int`: a sort's denotation is shown as the type
it reduces to.
-/

section variable [Ω]

/--
error: Application type mismatch: The argument
  ks
has type
  Kids Rat
but is expected to have type
  Kids Int
in the application
  some ks

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example (v : V .bool) : Option (Kids Int) :=
  match v with
  | .lt .real ks => some ks
  | _ => none

/--
error: Application type mismatch: The argument
  ks
has type
  Kids (Set Int)
but is expected to have type
  Kids (Set Rat)
in the application
  some ks

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example (v : V .bool) : Option (Kids (Set Rat)) :=
  match v with
  | .equal (.set .int) ks => some ks
  | _ => none

end

/-! ## Containers denote their own types

A set's denotation is the set type itself, its element's order included — a record's and a tuple's
order being the lexicographic one a user's own `Set (Record …)` or `Set (Int × Bool)` is built with
— so a set-sorted kid needs no cast.
-/

/-- info:
sets of integers : #[s, t]
sets of records  : #[r, q]
sets of pairs    : #[u, w]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Term.mkSymbolAs (Set Int) "s"
  let t ← Term.mkSymbolAs (Set Int) "t"
  let r ← Term.mkSymbolAs (Set (Record [("a", Int), ("b", Bool)])) "r"
  let q ← Term.mkSymbolAs (Set (Record [("a", Int), ("b", Bool)])) "q"
  let u ← Term.mkSymbolAs (Set (Int × Bool)) "u"
  let w ← Term.mkSymbolAs (Set (Int × Bool)) "w"
  for eq in [← smt! s = t, ← smt! r = q, ← smt! u = w] do
    match ← V.of .bool eq with
    | .equal (.set .int) ks =>
      let sets : Array (Term (Set Int)) := ks.val
      println! "sets of integers : {sets}"
    | .equal (.set (.record [("a", .int), ("b", .bool)])) ks =>
      let sets : Array (Term (Set (Record [("a", Int), ("b", Bool)]))) := ks.val
      println! "sets of records  : {sets}"
    | .equal (.set (.prod [.int, .bool])) ks =>
      let sets : Array (Term (Set (Int × Bool))) := ks.val
      println! "sets of pairs    : {sets}"
    | _ => println! "something else"

/-! A record denotes its own Lean type too, so matching a field read's record sort refines the term
it is read off to a `Term (Record …)`, whose fields `recordFields?` then reads by name. -/

/-- info: field a of a record whose b is true -/
#guard_msgs in #eval Env.runIO do
  let r ← smt! {a := 7, b := true}
  match ← V.of .int (← smt! ![return r].a) with
  | .selectField field (.record [("a", .int), ("b", .bool)]) arg =>
    let some fs ← arg.recordFields? | println! "not a literal"
    println! "field {field} of a record whose b is {fs.get "b"}"
  | _ => println! "something else"



/-! ## Kind ownership

A kind is taken apart by one view only. `def.term_view` refuses to route a kind to two, naming both,
before it emits anything: here a second view claiming `ITE`.
-/

public section variable [Ω]

/-- A second view of `ITE`. -/
inductive Clash : Typ → Type where
  /-- An if-then-else. -/
  | ite2 {τ : Typ} (c : Term Bool) (a b : Term τ.Denote) : Clash τ

/-- Takes nothing apart: only its registration matters here. -/
def Clash.of (τ : Typ) (_ : Term τ.Denote) : Env (Option (Clash τ)) := return none

end

register_typed_view% Cvc.Tests.Typed.View.Clash [ite2 ITE]

public section variable [Ω]

/-- error: `Clashing`: kind `ITE` is owned by both `Cvc.Typed.View.Bool` and `Cvc.Tests.Typed.View.Clash` -/
#guard_msgs in
def.term_view Clashing

end
