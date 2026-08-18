/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core
import Cvc.Untyped.Theory
import Cvc.Untyped.Core.Bool
import Cvc.Types.Set
-- the `match` notation expands to `Cvc.Untyped.Term.…` names that live here, and a macro's
-- names resolve at the use site
import Cvc.Untyped.Theory.Datatype

public meta import Cvc.Untyped.Theory.Datatype
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory
public meta import Cvc.Untyped.Core.Bool
public meta import Cvc.Types.Set



/-! # The `smt!` DSL, sort-erased

The grammar here is *generated*: each operator's notation comes from its `op%` entry and is emitted
alongside its untyped constructor, in that operator's own theory module. `open Cvc.Untyped`
selects this layer's `smt!`, which expands to fully-qualified `Cvc.Untyped.Term.…` calls, so
nothing else has to be in scope.
-/
namespace Cvc.Tests.Untyped.Term.Ext

open Cvc
open Cvc.Untyped

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
nary or  : (or a b a)
nary eq  : (and (= i j) (= j i))
add      : (+ i j)
prec     : (+ i (* j i))
paren    : (* (+ i j) i)
unary -  : (- i)
literals : (+ 3 i)
bool lit : (and a true)
string   : "hello"
ite      : (ite a i j)
let      : (< (+ i j) i)
escape   : (+ i j)
bitvec   : (bvadd u u)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Untyped.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Untyped.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let j ← Cvc.Untyped.Term.mkSymbolAs Int "j"
  let u ← Cvc.Untyped.Term.mkSymbolAs (BitVec 4) "u"

  println! "and      : {← smt! a ∧ b}"
  println! "or       : {← smt! a ∨ b}"
  println! "xor      : {← smt! a ⊻ b}"
  println! "implies  : {← smt! a → b}"
  println! "not      : {← smt! ¬ a}"
  println! "nested   : {← smt! ¬ (a ∨ b)}"
  println! "equal    : {← smt! i = j}"
  println! "distinct : {← smt! i ≠ j}"
  println! "nary and : {← smt! ∧[a, b, a]}"
  println! "nary or  : {← smt! ∨[a, b, a]}"
  println! "nary eq  : {← smt! =[i, j, i]}"
  println! "add      : {← smt! i + j}"
  println! "prec     : {← smt! i + j * i}"
  println! "paren    : {← smt! (i + j) * i}"
  println! "unary -  : {← smt! - i}"
  println! "literals : {← smt! 3 + i}"
  println! "bool lit : {← smt! a ∧ true}"
  println! "string   : {← smt! "hello"}"
  println! "ite      : {← smt! if a then i else j}"
  println! "let      : {← smt! let x ← i + j; x < i}"
  println! "escape   : {← smt! ![Cvc.Untyped.Term.add i j]}"
  println! "bitvec   : {← smt! ![Cvc.Untyped.Term.bvAdd u u]}"

-- associativity follows the `op%` entry: `∧` is `infixr`, `-` is `infixl`
/-- info:
right-assoc ∧ : (and a (and b a))
left-assoc  - : (- (- i j) i)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Untyped.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Untyped.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let j ← Cvc.Untyped.Term.mkSymbolAs Int "j"
  println! "right-assoc ∧ : {← smt! a ∧ b ∧ a}"
  println! "left-assoc  - : {← smt! i - j - i}"

/-! ## Application

`f i b` is spelled as Lean spells it, and expands to `applyN`, so it **flattens**: the nested
spelling `(f i) b` builds the very same term rather than a function-sorted intermediate. Arguments
parse at `max`, so an operator, `if`, `let` or `match` in argument position needs parentheses —
again exactly as in Lean.
-/

/-- info:
apply      : (f i b)
partial    : (f i)
nested     : (f i b)
flattens   : true
arg expr   : (f (+ i 1) b)
in expr    : (+ (f i b) 1)
under ¬    : (not (= (f i b) 1))
higher-ord : (hof f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Untyped.Term.mkSymbolAs (Int → Bool → Int) "f"
  let hof ← Cvc.Untyped.Term.mkSymbolAs ((Int → Bool → Int) → Int) "hof"
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let b ← Cvc.Untyped.Term.mkSymbolAs Bool "b"

  let flat ← smt! f i b
  let nested ← smt! (f i) b
  println! "apply      : {flat}"
  println! "partial    : {← smt! f i}"
  println! "nested     : {nested}"
  println! "flattens   : {flat == nested}"
  println! "arg expr   : {← smt! f (i + 1) b}"
  println! "in expr    : {← smt! (f i b) + 1}"
  println! "under ¬    : {← smt! ¬ (f i b) = 1}"
  println! "higher-ord : {← smt! hof f}"

/-! ## Notation that borrows Lean's own spelling

`%` and the five bit-vector operators carry the symbols Lean gives the corresponding operations, at
Lean's own precedences, so an expression reads the same in either language. `⊎` is multiset union,
which is what `bagUnionDisjoint` is.

Only `bagUnionDisjoint` is `nary`, so it is the only one of these with a bracket form — the others
gain a notation and nothing else.
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
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let j ← Cvc.Untyped.Term.mkSymbolAs Int "j"
  let u ← Cvc.Untyped.Term.mkSymbolAs (BitVec 4) "u"
  let v ← Cvc.Untyped.Term.mkSymbolAs (BitVec 4) "v"
  let s ← Cvc.Untyped.Term.mkSymbolAs (Cvc.Bag Int) "s"
  let t ← Cvc.Untyped.Term.mkSymbolAs (Cvc.Bag Int) "t"

  println! "mod         : {← smt! i % j}"
  println! "bv and      : {← smt! u &&& v}"
  println! "bv or       : {← smt! u ||| v}"
  println! "bv xor      : {← smt! u ^^^ v}"
  println! "bv shl      : {← smt! u <<< v}"
  println! "bv lshr     : {← smt! u >>> v}"
  println! "||| under &&&: {← smt! u ||| v &&& u}"
  println! "&&& under <<<: {← smt! u &&& v <<< u}"
  println! "bag union   : {← smt! s ⊎ t}"
  println! "bag nary    : {← smt! ⊎[s, t, s]}"

/-! ## Real literals

A decimal or exponent literal expands to `mkReal`, and the literal is elaborated against that
function's `Rat` argument — so cvc5 prints the exact rational, never a float.
-/

/-- info:
real     : (/ 3 2)
exponent : (/ 3 2000)
in expr  : (+ (/ 3 2) (/ 5 2))
with sym : (< r (/ 3 2))
-/
#guard_msgs in #eval Env.runIO do
  let r ← Cvc.Untyped.Term.mkSymbolAs Rat "r"

  println! "real     : {← smt! 1.5}"
  println! "exponent : {← smt! 1.5e-3}"
  println! "in expr  : {← smt! 1.5 + 2.5}"
  println! "with sym : {← smt! r < 1.5}"

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
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let s ← Cvc.Untyped.Term.mkSymbolAs (Cvc.Set Int) "s"
  let t ← Cvc.Untyped.Term.mkSymbolAs (Cvc.Set Int) "t"
  let q ← Cvc.Untyped.Term.mkSymbolAs (Array Int) "q"
  let r ← Cvc.Untyped.Term.mkSymbolAs (Array Int) "r"

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

`match … with` binds each constructor's fields for the writer, so a match reads the way Lean's
does and no bound variable has to be made by hand. The printed term shows the variables under the
names they were written with.

The catch-all is `_`. A bare identifier is always a constructor name, so `| nil => …` is the
nullary constructor and not a variable.
-/

/-- Declares a recursive list of integers, `nil | cons (head : Int) (tail : Lst)`. -/
def declareLst [Ω] : Env Srt := do
  let nil ← Cvc.Datatype.Ctor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Ctor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Datatype.Decl.mk "Lst"
  Srt.datatype (← (← decl.addCtor nil).addCtor cons)

/-- info:
match     : (match l (((cons h t) h) (nil 0)))
head of l : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let lst ← declareLst
  let l ← s.declareConst "l" lst

  let m ← smt!
    match l with
    | cons h t => h
    | nil => 0
  println! "match     : {m}"

  -- `l` is a one-element list, so the match takes the `cons` branch
  let dt ← lst.getDatatype
  let nilT ← Term.applyCtor (← (← dt.getCtorNamed "nil").getTerm)
  let seven ← Term.applyCtor (← (← dt.getCtorNamed "cons").getTerm)
    #[← Term.mkInt 7, nilT]
  (do Term.equal l seven) >>= s.assert
  s.checkSat (ifSat := do println! "head of l : {← s.getValueAs Int m}")

/-! A bound variable is an ordinary term in the body, so the operators and the rest of the DSL
apply to it — including a nested `match` on a field of the same datatype.
-/

/-- info:
arithmetic : (match l (((cons h t) (+ (* h 2) 1)) (nil 0)))
catch-all  : (match l (((cons h t) h) (_ 0)))
nested     : (match l (((cons h t) (match t (((cons h t) h) (_ 0)))) (_ 0)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let l ← s.declareConst "l" (← declareLst)

  println! "arithmetic : {← smt!
    match l with
    | cons h t => h * 2 + 1
    | nil => 0}"

  println! "catch-all  : {← smt!
    match l with
    | cons h t => h
    | _ => 0}"

  println! "nested     : {← smt!
    match l with
    | cons h t =>
      match t with
      | cons h t => h
      | _ => 0
    | _ => 0}"

/-! What the expansion checks, and what it leaves to cvc5. -/

/-- info:
unknown ctor : [internal] no constructor snoc for datatype Lst exists, among { nil cons }
wrong width  : constructor `cons` takes 2 field(s), bound 1
not datatype : cannot match on a term of sort `Int`, which is not a datatype
non-exhaustive: [internal] cases for match term are not exhaustive
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let l ← s.declareConst "l" (← declareLst)
  let i ← s.declareConst "i" (← Srt.int)
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"

  println! "unknown ctor : {← caught do pure s!"{← smt! match l with | snoc h t => h}"}"
  println! "wrong width  : {← caught do pure s!"{← smt! match l with | cons h => h}"}"
  println! "not datatype : {← caught do pure s!"{← smt! match i with | cons h t => h}"}"
  println! "non-exhaustive: {← caught do pure s!"{← smt! match l with | cons h t => h}"}"

/-! What the *expansion* rejects, before anything is built. -/

section rejected
variable [Ω] (l : Term)

/-- error:
a sort ascription has no meaning in the sort-erased layer, where a field's sort comes from the
datatype's declaration
-/
#guard_msgs in example : Env Term := smt! match l with | cons h (t : Nat) => h

end rejected

/-! ## Hygiene

A pattern binds under the name it was written with and nothing else. The expansion's own names are
macro-scoped, so they cannot capture one, and a pattern variable shadows an outer binding only
inside its own body.
-/

-- the Lean name `h` is bound outside to a constant printing as `outerH`, so the `cons` body
-- showing `h` is the pattern's variable and the catch-all showing `outerH` is the outer one
/-- info:
shadowing : (match l (((cons h t) h) (_ outerH)))
outer     : outerH
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let l ← s.declareConst "l" (← declareLst)
  let h ← s.declareConst "outerH" (← Srt.int)
  println! "shadowing : {← smt!
    match l with
    | cons h t => h
    | _ => ![pure h]}"
  println! "outer     : {h}"



/-! ## Records

`{a := 7, b := tru}` is Lean's structure-instance syntax. A field may state its sort or leave it
out: left out it is the sort the field's term turns out to have, stated it is *checked* against
that, so an annotation can only confirm what is there.
-/

/-- info:
record : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
sort   : __cvc5_record_a_Int_b_Bool
a      : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
b      : (b (__cvc5_record_a_Int_b_Bool_ctor 7 true))
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let r ← smt! {a : int := 7, b : bool := true}
  println! "record : {r}"
  println! "sort   : {← r.getSort}"
  println! "a      : {← r.recordGet "a"}"
  println! "b      : {← r.recordGet "b"}"

/-! **Field order is part of the sort**, unlike Lean's structure instances: the same fields written
the other way round denote a different sort, and cvc5 refuses to mix their terms. -/

/-- info:
in order : __cvc5_record_a_Int_b_Bool
swapped  : __cvc5_record_b_Bool_a_Int
same     : false
mixed    : rejected
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let r ← smt! {a : int := 7, b : bool := true}
  let r' ← smt! {b : bool := true, a : int := 7}
  println! "in order : {← r.getSort}"
  println! "swapped  : {← r'.getSort}"
  println! "same     : {(← r.getSort) == (← r'.getSort)}"
  println! "mixed    : {← (try (do let _ ← smt! ![pure r] = ![pure r']; pure "accepted")
    catch _ => pure "rejected")}"

/-! A field's term is an ordinary `smtTerm`, so it may be any expression the DSL can write, and a
record may be a field of a record. -/

/-- info:
computed : (__cvc5_record_a_Int_b_Bool_ctor (+ 1 2) (not true))
nested   : (__cvc5_record_inner___cvc5_record_a_Int_tag_Int_ctor (__cvc5_record_a_Int_ctor 7) 1)
inner a  : (a (inner (__cvc5_record_inner___cvc5_record_a_Int_tag_Int_ctor (__cvc5_record_a_Int_ctor 7) 1)))
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  println! "computed : {← smt! {a : int := 1 + 2, b : bool := ¬ true}}"

  let inner ← smt! {a : int := 7}
  let innerSrt ← inner.getSort
  let outer ← smt! {inner : innerSrt := ![pure inner], tag : int := 1}
  println! "nested   : {outer}"
  println! "inner a  : {← (← outer.recordGet "inner").recordGet "a"}"

/-! A record literal is at maximum precedence, so it is an argument of an operator or an
application with no parentheses. -/

/-- info:
as operand : (= (__cvc5_record_a_Int_ctor 7) (__cvc5_record_a_Int_ctor 8))
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  println! "as operand : {← smt! {a : int := 7} = {a : int := 8}}"

/-! There is no syntax for the empty record: `{}` fails to parse, with `expected smtRecField`. That
cannot be pinned here — a parse error aborts before `#guard_msgs` can see any message — but
`Srt.record` refuses an empty record whatever path reaches it, which the sort tests do pin.
-/


/-! A field's sort may be stated, inferred, or some of each, and all three build the same record. -/

/-- info:
annotated : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
inferred  : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
mixed     : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
same sort : true
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let annotated ← smt! {a : int := 7, b : bool := true}
  let inferred ← smt! {a := 7, b := true}
  println! "annotated : {annotated}"
  println! "inferred  : {inferred}"
  println! "mixed     : {← smt! {a := 7, b : bool := true}}"
  println! "same sort : {(← annotated.getSort) == (← inferred.getSort)}"

/-! A stated sort that disagrees with its term is caught before the record is built, naming the
field — this is `Term.mkRecord`'s own check, the record's sort having been built from what was
stated. -/

/-- info:
wrong sort : caught: field `a` of record `__cvc5_record_a_Bool` has sort `Bool`, but `7` has sort `Int`
-/
#guard_msgs in #eval Env.runIO do
  let bool ← Srt.bool
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"
  println! "wrong sort : {← caught do pure s!"{← smt! {a : bool := 7}}"}"



/-! ## Projection

`r.a` reads field `a` off `r`. It arrives as one identifier token, so whether it names something or
reads a field off something is settled by *resolution*, in Lean's own order: a local head first,
then the longest prefix that resolves.
-/

/-- info:
local    : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
nested   : (a (inner (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)))
operand  : (+ (a (__cvc5_record_a_Int_b_Bool_ctor 7 true)) 1)
plain    : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
-/
#guard_msgs in #eval Env.runIO do
  let r ← smt! {a := 7, b := true}
  println! "local    : {← smt! r.a}"
  let n ← smt! {inner := ![pure r], tag := 1}
  println! "nested   : {← smt! n.inner.a}"
  println! "operand  : {← smt! r.a + 1}"
  -- an identifier naming no field is still just an identifier
  println! "plain    : {← smt! r}"

/-! A head that is not an identifier gets there by a different route — the lexer fuses `r.a` into
one token but cannot fuse `).a`, so those are an ordinary grammar rule. `smt! r .a`, with a space,
is neither and does not parse. -/

/-- info:
paren    : (a (__cvc5_record_a_Int_ctor 1))
escape   : (b (__cvc5_record_a_Int_b_Bool_ctor 7 true))
literal  : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
-/
#guard_msgs in #eval Env.runIO do
  let r ← smt! {a := 7, b := true}
  println! "paren    : {← smt! ({a := 1}).a}"
  println! "escape   : {← smt! ![pure r].b}"
  println! "literal  : {← smt! {a := 7, b := true}.a}"

/-! Resolution order is Lean's. A **local** head wins even where a constant of the whole name
exists, so `r.a` below reads a field rather than naming `Cvc.Tests.Untyped.Ext.r.a`. -/

/-- A constant whose name is a local's name plus a field's. -/
def r.a : Nat := 0

/-- info: local wins : (a (__cvc5_record_a_Int_ctor 7)) -/
#guard_msgs in #eval Env.runIO do
  let r ← smt! {a := 7}
  println! "local wins : {← smt! r.a}"

/-! With no local in the way, the whole name resolves — this one is a `Nat`, so it fails as a
*term* rather than as an unknown identifier, which is what shows it was not taken apart. -/

/--
error: Application type mismatch: The argument
  r.a
has type
  Nat
but is expected to have type
  Term
in the application
  pure r.a

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 3
-/
#guard_msgs in
example [Ω] : Env Term := smt! r.a

/-! A field that is not there is a runtime error here, naming the record's fields — sort-erased
there is nothing to catch it earlier. -/

/-- info: no field : caught: record sort `__cvc5_record_a_Int` has no field named `zzz`, its fields are `a` -/
#guard_msgs in #eval Env.runIO do
  let rec' ← smt! {a := 7}
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"
  println! "no field : {← caught do pure s!"{← smt! rec'.zzz}"}"



/-! ## Updates

`{r with a := 9}` replaces a field, and chains for several. A field may state its sort here too,
though the record already fixes it, and naming a field twice is refused as the literal is expanded.
-/

/-- info:
one       : ((_ update a) (__cvc5_record_a_Int_b_Bool_ctor 7 true) 9)
two       : ((_ update b) ((_ update a) (__cvc5_record_a_Int_b_Bool_ctor 7 true) 9) false)
annotated : ((_ update a) (__cvc5_record_a_Int_b_Bool_ctor 7 true) 9)
sort kept : true
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let r ← smt! {a := 7, b := true}
  println! "one       : {← smt! {r with a := 9}}"
  println! "two       : {← smt! {r with a := 9, b := false}}"
  println! "annotated : {← smt! {r with a : int := 9}}"
  println! "sort kept : {(← (← smt! {r with a := 9}).getSort) == (← r.getSort)}"

/-- info:
wrong sort : caught: field `a` is stated at sort `Bool`, but its term has sort `Int`
no field   : caught: record sort `__cvc5_record_a_Int_b_Bool` has no field named `zzz`, its fields are `a`, `b`
-/
#guard_msgs in #eval Env.runIO do
  let bool ← Srt.bool
  let r ← smt! {a := 7, b := true}
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"
  println! "wrong sort : {← caught do pure s!"{← smt! {r with a : bool := 9}}"}"
  println! "no field   : {← caught do pure s!"{← smt! {r with zzz := 9}}"}"

/-! Naming a field twice would silently overwrite, so it is refused where it is written. -/

/--
error: record update names field `a` more than once
-/
#guard_msgs in
example [Ω] (r : Term) : Env Term := smt! {r with a := 9, a := 8}



/-! ### `|>.`, Lean's pipeline projection

`e |>.a` is `(e).a`, and it is Lean's `pipeProj` at Lean's own precedence: **minimum**, so it takes
everything to its left. That is what the form is for — an application head needs no parentheses.
-/

/-- info:
application : (a (f 1))
literal     : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
chained     : (a (inner (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)))
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let r ← smt! {a := 7, b := true}
  let s ← Solver.new
  let f ← s.declareFun "f" #[int] (← r.getSort)
  println! "application : {← smt! f 1 |>.a}"
  println! "literal     : {← smt! {a := 7, b := true} |>.a}"
  let n ← smt! {inner := ![pure r], tag := 1}
  println! "chained     : {← smt! ![pure n] |>.inner |>.a}"

/-! Taking everything to the left is Lean's reading and not always the wanted one: `r.a + 1 |>.b`
is `(r.a + 1).b`. It is nearly always a mistake here, an arithmetic term having no fields — but a
loud one, which is why matching Lean is worth more than optimising for it. -/

/-- info: minPrec : caught: expected a record sort, got `Int` -/
#guard_msgs in #eval Env.runIO do
  let r ← smt! {a := 7, b := true}
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"
  println! "minPrec : {← caught do pure s!"{← smt! r.a + 1 |>.b}"}"
