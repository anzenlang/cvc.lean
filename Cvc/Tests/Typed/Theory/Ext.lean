/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Core.Bool
import Cvc.Types.Set
-- the `match` notation expands to `Cvc.Typed.…` names that live here, and a macro's names
-- resolve at the use site
import Cvc.Typed.Theory.Datatype

public meta import Cvc.Typed.Theory.Datatype
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Core.Bool
public meta import Cvc.Types.Set



/-! # The `smt!` DSL, typed

Same generated grammar as the sort-erased layer — it is emitted once, alongside the untyped
constructors, and inherited here because a typed theory module imports its untyped counterpart.
Only the expansion differs: `open Cvc.Typed` selects a `smt!` that expands to
fully-qualified `Cvc.Typed.Term.…` calls, so the resulting terms carry their Lean index.
-/
namespace Cvc.Tests.Typed.Term.Ext

open Cvc
open Cvc.Typed

/-- info:
and      : (and a b)
or       : (or a b)
xor      : (xor a b)
implies  : (=> a b)
not      : (not a)
nested   : (not (or a b))
equal    : (= i j)
distinct : (distinct i j)
nary and : (and a b a)
nary eq  : (and (= i j) (= j i))
add      : (+ i j)
prec     : (+ i (* j i))
paren    : (* (+ i j) i)
unary -  : (- i)
rat neg  : (- r)
literals : (+ 3 i)
bool lit : (and a true)
compare  : (< i j)
ite      : (ite a i j)
let      : (< (+ i j) i)
escape   : (+ i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Typed.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Typed.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Typed.Term.mkSymbolAs Int "j"
  let r ← Cvc.Typed.Term.mkSymbolAs Rat "r"

  println! "and      : {← smt! a ∧ b}"
  println! "or       : {← smt! a ∨ b}"
  println! "xor      : {← smt! a ⊻ b}"
  println! "implies  : {← smt! a → b}"
  println! "not      : {← smt! ¬ a}"
  println! "nested   : {← smt! ¬ (a ∨ b)}"
  println! "equal    : {← smt! i = j}"
  println! "distinct : {← smt! i ≠ j}"
  println! "nary and : {← smt! ∧[a, b, a]}"
  println! "nary eq  : {← smt! =[i, j, i]}"
  println! "add      : {← smt! i + j}"
  println! "prec     : {← smt! i + j * i}"
  println! "paren    : {← smt! (i + j) * i}"
  println! "unary -  : {← smt! - i}"
  println! "rat neg  : {← smt! - r}"
  println! "literals : {← smt! 3 + i}"
  println! "bool lit : {← smt! a ∧ true}"
  println! "compare  : {← smt! i < j}"
  println! "ite      : {← smt! if a then i else j}"
  println! "let      : {← smt! let x ← i + j; x < i}"
  println! "escape   : {← smt! ![Cvc.Typed.Term.add i j]}"

-- associativity follows the `op%` entry: `∧` is `infixr`, `-` is `infixl`
/-- info:
right-assoc ∧ : (and a (and b a))
left-assoc  - : (- (- i j) i)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Typed.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Typed.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Typed.Term.mkSymbolAs Int "j"
  println! "right-assoc ∧ : {← smt! a ∧ b ∧ a}"
  println! "left-assoc  - : {← smt! i - j - i}"

/-! ## Application

`f i b` is spelled as Lean spells it, and expands to `applyN` over an `Args` spine, so the index
follows the arrows the arguments consume: saturating gives the codomain, stopping early gives the
*remaining* function index. It flattens, inheriting that from the sort-erased constructor.
-/

/-- info:
apply      : (f i b)
partial    : (f i)
nested     : (f i b)
flattens   : true
arg expr   : (f (+ i 1) b)
in expr    : (+ (f i b) 1)
higher-ord : (hof f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Typed.Term.mkSymbolAs (Int → Bool → Int) "f"
  let hof ← Cvc.Typed.Term.mkSymbolAs ((Int → Bool → Int) → Int) "hof"
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let b ← Cvc.Typed.Term.mkSymbolAs Bool "b"

  let flat : Term Int ← smt! f i b
  let nested : Term Int ← smt! (f i) b
  println! "apply      : {flat}"
  println! "partial    : {← (smt! f i : Env (Term (Bool → Int)))}"
  println! "nested     : {nested}"
  println! "flattens   : {flat == nested}"
  println! "arg expr   : {← (smt! f (i + 1) b : Env (Term Int))}"
  println! "in expr    : {← (smt! (f i b) + 1 : Env (Term Int))}"
  println! "higher-ord : {← (smt! hof f : Env (Term Int))}"



/-! ## Notation that borrows Lean's own spelling

`%` and the five bit-vector operators carry the symbols Lean gives the corresponding operations, at
Lean's own precedences. `⊎` is multiset union, which is what `bagUnionDisjoint` is, and being the
only `nary` one of the six it is the only one with a bracket form.
-/

/-- info:
mod         : (mod i j)
bv and      : (bvand u v)
bv or       : (bvor u v)
bv xor      : (bvxor u v)
bv shl      : (bvshl u v)
bv lshr     : (bvlshr u v)
||| under &&&: (bvor u (bvand v u))
&&& under <<<: (bvand u (bvshl v u))
bag union   : (bag.union_disjoint s t)
bag nary    : (bag.union_disjoint (bag.union_disjoint s t) s)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Typed.Term.mkSymbolAs Int "j"
  let u ← Cvc.Typed.Term.mkSymbolAs (BitVec 4) "u"
  let v ← Cvc.Typed.Term.mkSymbolAs (BitVec 4) "v"
  let s ← Cvc.Typed.Term.mkSymbolAs (Cvc.Bag Int) "s"
  let t ← Cvc.Typed.Term.mkSymbolAs (Cvc.Bag Int) "t"

  println! "mod         : {← (smt! i % j : Env (Term Int))}"
  println! "bv and      : {← (smt! u &&& v : Env (Term (BitVec 4)))}"
  println! "bv or       : {← (smt! u ||| v : Env (Term (BitVec 4)))}"
  println! "bv xor      : {← (smt! u ^^^ v : Env (Term (BitVec 4)))}"
  println! "bv shl      : {← (smt! u <<< v : Env (Term (BitVec 4)))}"
  println! "bv lshr     : {← (smt! u >>> v : Env (Term (BitVec 4)))}"
  println! "||| under &&&: {← (smt! u ||| v &&& u : Env (Term (BitVec 4)))}"
  println! "&&& under <<<: {← (smt! u &&& v <<< u : Env (Term (BitVec 4)))}"
  println! "bag union   : {← (smt! s ⊎ t : Env (Term (Cvc.Bag Int)))}"
  println! "bag nary    : {← (smt! ⊎[s, t, s] : Env (Term (Cvc.Bag Int)))}"

/-! ## Real literals

A decimal or exponent literal expands to `mkReal`, whose `Rat` argument the literal is elaborated
against — so the term lands at `Term Rat` and cvc5 prints the exact rational.
-/

/-- info:
real     : (/ 3 2)
exponent : (/ 3 2000)
in expr  : (+ (/ 3 2) (/ 5 2))
with sym : (< r (/ 3 2))
-/
#guard_msgs in #eval Env.runIO do
  let r ← Cvc.Typed.Term.mkSymbolAs Rat "r"

  println! "real     : {← (smt! 1.5 : Env (Term Rat))}"
  println! "exponent : {← (smt! 1.5e-3 : Env (Term Rat))}"
  println! "in expr  : {← (smt! 1.5 + 2.5 : Env (Term Rat))}"
  println! "with sym : {← (smt! r < 1.5 : Env (Term Bool))}"



/-! ## The DSL carries the typed index

Each of these pins the index the expansion produces. They typecheck by delegation, with no
coercion.
-/

section indices
variable [Ω] (a b : Term Bool) (i j : Term Int) (r : Term Rat) (u v : Term (BitVec 4))
variable (f : Term (Int → Bool → Int))

/-- A connective stays at `Bool`. -/
example : Env (Term Bool) := smt! a ∧ b
/-- A comparison drops from `Int` to `Bool`. -/
example : Env (Term Bool) := smt! i < j
/-- Arithmetic stays at its operands' index. -/
example : Env (Term Int) := smt! i + j * i
/-- …including over the reals. -/
example : Env (Term Rat) := smt! - r
/-- `ite` takes its index from its branches. -/
example : Env (Term Int) := smt! if a then i else j
/-- A `let` binding is indexed too. -/
example : Env (Term Bool) := smt! let x ← i + j; x < i
/-- An n-ary equality over `Int` still lands in `Bool`. -/
example : Env (Term Bool) := smt! =[i, j, i]
/-- Escaping keeps whatever index the Lean term has. -/
example : Env (Term (BitVec 4)) := smt! ![Cvc.Typed.Term.bvAdd u v]
/-- A real literal lands at `Rat`, not at `Int`. -/
example : Env (Term Rat) := smt! 1.5 + 2.5
/-- The bit-vector notations keep the width. -/
example : Env (Term (BitVec 4)) := smt! u &&& v <<< u
/-- A saturating application lands at the function's codomain. -/
example : Env (Term Int) := smt! f i b
/-- A partial one keeps the arrows its arguments did not consume. -/
example : Env (Term (Bool → Int)) := smt! f i
/-- An application is an operand like any other. -/
example : Env (Term Bool) := smt! (f i b) < j

end indices

/-! ## Notation from the container theories

`∈`, `⊆`, `∪`, `∩`, `∖` and `++` come from the `op%` entries of the set and sequence theories, so
their grammar is compiled with those theories rather than with the DSL.
-/

/-- info:
member    : (set.member i s)
subset    : (set.subset s t)
union     : (set.union s t)
inter     : (set.inter s t)
minus     : (set.minus s t)
union prec: (set.union s (set.inter t s))
unionN    : (set.union (set.union s t) s)
interN    : (set.inter (set.inter s t) s)
seq concat: (seq.++ q r)
concatN   : (seq.++ q r q)
mixed     : (and (set.member i s) (set.subset s t))
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let s ← Cvc.Typed.Term.mkSymbolAs (Cvc.Set Int) "s"
  let t ← Cvc.Typed.Term.mkSymbolAs (Cvc.Set Int) "t"
  let q ← Cvc.Typed.Term.mkSymbolAs (Array Int) "q"
  let r ← Cvc.Typed.Term.mkSymbolAs (Array Int) "r"

  println! "member    : {← smt! i ∈ s}"
  println! "subset    : {← smt! s ⊆ t}"
  println! "union     : {← smt! s ∪ t}"
  println! "inter     : {← smt! s ∩ t}"
  println! "minus     : {← smt! s ∖ t}"
  println! "union prec: {← smt! s ∪ t ∩ s}"
  println! "unionN    : {← smt! ∪[s, t, s]}"
  println! "interN    : {← smt! ∩[s, t, s]}"
  println! "seq concat: {← smt! q ++ r}"
  println! "concatN   : {← smt! ++[q, r, q]}"
  println! "mixed     : {← smt! (i ∈ s) ∧ (s ⊆ t)}"



/-! ## Matching

The same notation as the sort-erased layer, expanding to `Datatype.Ctor.caseErased`, which checks
the arity and the variables' sorts. Each variable's **index is inferred from the body**, so a match
reads exactly as it does sort-erased while every bound variable carries its Lean type.

Every field is bound sort-erased, at the sort the declaration gives it, and only the ones the body
mentions are re-typed. So a field the body ignores — the tail of a list, most of the time —
costs nothing, though it has no index to infer one from.

A variable may state its sort, `| cons (h : Int) t => …`, which then becomes a check against the
declaration. That is what a variable the body mentions in a position that does not pin its index
down needs.
-/

/-- The Lean index standing for the SMT datatype `Lst`. -/
structure Lst where private mk ::
  deriving DecidableEq, Ord, Hashable

instance : ToTyp Lst := ⟨.datatype "Lst"⟩

/-- Declares the datatype the `Lst` index names, `nil | cons (head : Int) (tail : Lst)`. -/
def declareLst [Ω] : Env Srt := do
  let nil ← Cvc.Datatype.Ctor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Ctor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Datatype.Decl.mk "Lst"
  Srt.datatype (← (← decl.addCtor nil).addCtor cons)

/-- info:
match     : (match l (((cons h t) (+ (* h 2) 1)) (nil 0)))
head of l : 15
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let _ ← declareLst
  let l ← s.declareConst Lst "l"

  -- `h` is a `Term Int` in the body, so the arithmetic operators apply and the match is `Term Int`;
  -- `t` is never mentioned and needs no index
  let m ← smt!
    match l with
    | cons h t => h * 2 + 1
    | nil => 0
  println! "match     : {m.erase}"

  let consC ← Datatype.ctor Lst "cons"
  let seven ← consC.apply2 (← Term.mkInt 7) (← (← Datatype.ctor Lst "nil").apply)
  (do Term.equal l seven) >>= s.assert
  s.checkSat (ifSat := do println! "head of l : {← s.getValue m}")

/-- info:
catch-all : (match l (((cons h t) h) (_ 0)))
nested    : (match l (((cons h t) (match t (((cons h t) h) (_ 0)))) (_ 0)))
ascribed  : (match l (((cons h t) (+ h 1)) (_ 0)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let _ ← declareLst
  let l ← s.declareConst Lst "l"

  -- the index is stated here because nothing else says what it should be: the body is just `h`,
  -- so it takes the match's own expected type to pin it down
  let anyCase : Term Int ← smt!
    match l with
    | cons h t => h
    | _ => 0
  println! "catch-all : {anyCase.erase}"

  -- `t` states its index because the only thing mentioning it is the match that wants it; the
  -- inner `h` states its own because its index reaches it only through the outer match's expected
  -- type, which does not survive the nesting. The outer `h` states nothing and needs nothing: the
  -- inner pattern shadows it, so it is never referenced
  let nested : Term Int ← smt!
    match l with
    | cons h (t : Lst) =>
      match t with
      | cons (h : Int) t => h
      | _ => 0
    | _ => 0
  println! "nested    : {nested.erase}"

  -- an ascription is a check against the declaration
  println! "ascribed  : {(← smt!
    match l with
    | cons (h : Int) t => h + 1
    | _ => 0).erase}"

/-! The index a match carries, and what it rejects. -/

section indices
variable [Ω] (l : Term Lst) (b : Term Bool)

/-- A match answers at the index its bodies share. -/
example : Env (Term Int) := smt! match l with | cons h t => h | _ => 0
/-- …including at `Bool`. -/
example : Env (Term Bool) := smt! match l with | cons h t => ![pure b] | _ => true

-- a variable the body mentions is re-typed, so using it at the wrong index is a type error
/-- error: Application type mismatch: The argument
  smtArg0✝
has type
  Datatype.Case Lst Bool
but is expected to have type
  Datatype.Case Lst Int
in the application
  List.cons smtArg0✝
-/
#guard_msgs in
example : Env (Term Int) := smt! match l with | cons (h : Bool) t => h | _ => 0

end indices

/-- info:
wrong sort : caught: cannot type the following term as `Lst`, term has sort `Int`:
h
wrong width: caught: constructor `cons` takes 2 field(s), bound 1
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let _ ← declareLst
  let l ← s.declareConst Lst "l"
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"

  -- an ascription disagreeing with the declaration is caught where the variable is re-typed
  println! "wrong sort : {← caught do pure s!"{(← smt!
    match l with
    | cons (h : Lst) t => 0
    | _ => 0).erase}"}"
  println! "wrong width: {← caught do pure s!"{(← smt!
    match l with
    | cons h => h
    | _ => 0).erase}"}"



/-! ## Records

`{a := 7, b := tru}` is Lean's structure-instance syntax, and the index is inferred from the field
terms — this layer needs no sort stated anywhere. A field may state one anyway, in which case it is
*checked* against the index before the record is built.

**Field order is part of the sort**, unlike Lean's structure instances, and here it shows in the
index: the two orders are different Lean types.
-/

/-- info:
inferred  : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
a         : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
annotated : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
mixed     : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let r ← smt! {a := 7, b := true}
  println! "inferred  : {r}"
  println! "a         : {← r.recordGet "a"}"
  println! "annotated : {← smt! {a : int := 7, b : bool := true}}"
  println! "mixed     : {← smt! {a := 7, b : bool := true}}"

/-- The index really is inferred from the field terms, and carries their order. -/
example [Ω] : Env (Term (Record [("a", Int), ("b", Bool)])) := smt! {a := 7, b := true}
/-- The other order is a different index. -/
example [Ω] : Env (Term (Record [("b", Bool), ("a", Int)])) := smt! {b := true, a := 7}

/-- A field read off a literal comes back at its own type, with nothing ascribed. -/
example [Ω] : Env (Term Int) := do (← smt! {a := 7, b := true}).recordGet "a"

/-! A stated sort that disagrees with the index is caught before the record is built. Sort-erased
the same mistake is caught by `Term.mkRecord`; here there is no sort to build from, so the check
is its own. -/

/-- info:
wrong sort : caught: field `a` is stated at sort `Bool`, but its term has sort `Int`
-/
#guard_msgs in #eval Env.runIO do
  let bool ← Srt.bool
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"
  println! "wrong sort : {← caught do pure s!"{← smt! {a : bool := 7}}"}"



/-! ## Projection and updates

`r.a` reads field `a` off `r`, resolved exactly as in the sort-erased layer — a local head first,
then the longest prefix that resolves. What differs is what the result *is*: the index gives the
field's type, so a projection is an operand of that type's operators with nothing ascribed, and a
field that is not there does not compile.
-/

/-- info:
local    : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
nested   : (a (inner (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)))
operand  : (+ (a (__cvc5_record_a_Int_b_Bool_ctor 7 true)) 1)
paren    : (a (__cvc5_record_a_Int_ctor 1))
update   : ((_ update a) (__cvc5_record_a_Int_b_Bool_ctor 7 true) 9)
two      : ((_ update b) ((_ update a) (__cvc5_record_a_Int_b_Bool_ctor 7 true) 9) false)
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let r ← smt! {a := 7, b := true}
  println! "local    : {← smt! r.a}"
  let n ← smt! {inner := ![pure r], tag := 1}
  println! "nested   : {← smt! n.inner.a}"
  println! "operand  : {← smt! r.a + 1}"
  println! "paren    : {← smt! ({a := 1}).a}"
  println! "update   : {← smt! {r with a := 9}}"
  println! "two      : {← smt! {r with a := 9, b := false}}"
  -- an annotation here can only confirm what the index says
  let _ ← smt! {r with a : int := 9}

section signatures
variable [Ω] (r : Term (Record [("a", Int), ("b", Bool)]))

/-- A projection has the field's type. -/
example : Env (Term Int) := smt! r.a
/-- And an update has the record's. -/
example : Env (Term (Record [("a", Int), ("b", Bool)])) := smt! {r with a := 9}

end signatures

/-! A field that is not there does not compile, where sort-erased it is a runtime error. -/

/--
error: failed to synthesize instance of type class
  FieldOf [("a", Int), ("b", Bool)] "zzz" Int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Ω] (r : Term (Record [("a", Int), ("b", Bool)])) : Env (Term Int) := smt! r.zzz

/-! Naming a field twice in an update is refused as the literal is expanded. -/

/--
error: record update names field `a` more than once
-/
#guard_msgs in
example [Ω] (r : Term (Record [("a", Int)])) : Env (Term (Record [("a", Int)])) :=
  smt! {r with a := 9, a := 8}



/-! ### `|>.`, Lean's pipeline projection

`e |>.a` is `(e).a`, at Lean's own precedence — minimum, so it takes everything to its left. Typed
it is where the form earns most: an application head needs no parentheses, and the field still
comes back at the type the index gives it.
-/

/-- info:
application : (a (f 1))
literal     : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
chained     : (a (inner (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)))
-/
#guard_msgs in #eval Env.runIO do
  let r ← smt! {a := 7, b := true}
  let s ← Solver.new
  let f ← s.declareFun (α := Int → Record [("a", Int), ("b", Bool)]) "f"
  println! "application : {← smt! f 1 |>.a}"
  println! "literal     : {← smt! {a := 7, b := true} |>.a}"
  let n ← smt! {inner := ![pure r], tag := 1}
  println! "chained     : {← smt! ![pure n] |>.inner |>.a}"

/-- The index survives the pipe. -/
example [Ω] (r : Term (Record [("a", Int), ("b", Bool)])) : Env (Term Int) := smt! ![pure r] |>.a

/-! And a field that is not there still does not compile. -/

/--
error: failed to synthesize instance of type class
  FieldOf [("a", Int), ("b", Bool)] "zzz" Int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Ω] (r : Term (Record [("a", Int), ("b", Bool)])) : Env (Term Int) := smt! ![pure r] |>.zzz
