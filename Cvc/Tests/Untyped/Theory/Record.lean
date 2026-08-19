/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Record
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Theory.Record
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory



/-! # Records, sort-erased -/
namespace Cvc.Tests.Untyped.Record

open Cvc Untyped

/-- `{a : Int, b : Bool}`. -/
def srt [Ω] : Env Srt := do Srt.record #[("a", ← Srt.int), ("b", ← Srt.bool)]

/-- Catches a user error, so a rejection can be printed rather than propagated. -/
def caught [Ω] (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"



/-! ## What a record sort reflects to

A record is a datatype of one constructor, whose selectors are named after the fields. The
constructor's own name is cvc5's, which is why nothing here goes through it.
-/

/-- info:
sort    : __cvc5_record_a_Int_b_Bool
isRecord: true
ctor    : __cvc5_record_a_Int_b_Bool_ctor
  field : a : Int
  field : b : Bool
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  println! "sort    : {srt}"
  println! "isRecord: {srt.isRecord}"
  println! "ctor    : {← (← srt.recordCtor).getName}"
  for (name, fieldSrt) in ← srt.recordFields do
    println! "  field : {name} : {fieldSrt}"

/-! `recordCtor` refuses a sort that is not a record, rather than answering the constructor of
whatever datatype it was handed. -/

/-- info:
not a record : caught: expected a record sort, got `Int`
-/
#guard_msgs in #eval Env.runIO do
  println! "not a record : {← caught do pure s!"{← (← Srt.int).recordFields}"}"



/-! ## Building, reading, updating -/

/-- info:
record  : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
sort    : __cvc5_record_a_Int_b_Bool
a       : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
b       : (b (__cvc5_record_a_Int_b_Bool_ctor 7 true))
set a   : ((_ update a) (__cvc5_record_a_Int_b_Bool_ctor 7 true) 9)
sort    : __cvc5_record_a_Int_b_Bool
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  let r ← Term.mkRecord srt #[("a", ← Term.mkInt 7), ("b", ← Term.mkBool true)]
  println! "record  : {r}"
  println! "sort    : {← r.getSort}"
  println! "a       : {← r.recordGet "a"}"
  println! "b       : {← r.recordGet "b"}"
  let r' ← r.recordSet "a" (← Term.mkInt 9)
  println! "set a   : {r'}"
  println! "sort    : {← r'.getSort}"

/-! The fields may be given in any order — they are put in the order the sort fixes, which is the
order cvc5's constructor wants. That is what makes the one confusion a record invites impossible
here, field order being part of the sort. -/

/-- info:
same    : true
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  let inOrder ← Term.mkRecord srt #[("a", ← Term.mkInt 7), ("b", ← Term.mkBool true)]
  let swapped ← Term.mkRecord srt #[("b", ← Term.mkBool true), ("a", ← Term.mkInt 7)]
  println! "same    : {inOrder == swapped}"

/-! A field may itself be a record. -/

/-- info:
nested  : (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)
inner a : (a (inner (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)))
-/
#guard_msgs in #eval Env.runIO do
  let inner ← srt
  let outer ← Srt.record #[("inner", inner), ("tag", ← Srt.int)]
  let i ← Term.mkRecord inner #[("a", ← Term.mkInt 7), ("b", ← Term.mkBool true)]
  let o ← Term.mkRecord outer #[("inner", i), ("tag", ← Term.mkInt 1)]
  println! "nested  : {o}"
  println! "inner a : {← (← o.recordGet "inner").recordGet "a"}"



/-! ## What is checked, and what the message says

Each of these is cvc5's error made specific: it would otherwise report a swapped pair as
`[internal] bad type for constructor argument`, naming the mono-morphised datatype rather than the
field that is wrong.
-/

/-- info:
duplicate : caught: record `__cvc5_record_a_Int_b_Bool` given more than one value for field `a`
unknown   : caught: record sort `__cvc5_record_a_Int_b_Bool` has no field named `c`
missing   : caught: record `__cvc5_record_a_Int_b_Bool` given no value for field `b`
wrong srt : caught: field `a` of record `__cvc5_record_a_Int_b_Bool` has sort `Int`, but `true` has sort `Bool`
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  let seven ← Term.mkInt 7
  let tru ← Term.mkBool true
  let mk (fields : Array (String × Term)) : Env String := caught do
    pure s!"{← Term.mkRecord srt fields}"

  println! "duplicate : {← mk #[("a", seven), ("a", seven), ("b", tru)]}"
  println! "unknown   : {← mk #[("a", seven), ("b", tru), ("c", seven)]}"
  println! "missing   : {← mk #[("a", seven)]}"
  println! "wrong srt : {← mk #[("a", tru), ("b", seven)]}"

/-! Reading and updating are checked the same way, and a rejection names the record's fields. -/

/-- info:
get bad   : caught: record sort `__cvc5_record_a_Int_b_Bool` has no field named `c`, its fields are `a`, `b`
set bad   : caught: record sort `__cvc5_record_a_Int_b_Bool` has no field named `c`, its fields are `a`, `b`
set srt   : caught: field `a` of record `__cvc5_record_a_Int_b_Bool` has sort `Int`, but `true` has sort `Bool`
get plain : caught: expected a record sort, got `Int`
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  let r ← Term.mkRecord srt #[("a", ← Term.mkInt 7), ("b", ← Term.mkBool true)]
  println! "get bad   : {← caught do pure s!"{← r.recordGet "c"}"}"
  println! "set bad   : {← caught do pure s!"{← r.recordSet "c" (← Term.mkInt 9)}"}"
  println! "set srt   : {← caught do pure s!"{← r.recordSet "a" (← Term.mkBool true)}"}"
  println! "get plain : {← caught do pure s!"{← (← Term.mkInt 7).recordGet "a"}"}"



/-! ## Field order is part of the sort

Two records of the same fields in a different order are different sorts, and cvc5 rejects a term
mixing them.
-/

/-- info:
same sort : false
mixed     : caught: [internal] Subexpressions must have the same type:
Equation: (= (__cvc5_record_a_Int_b_Bool_ctor 7 true) (__cvc5_record_b_Bool_a_Int_ctor true 7))
Type 1: __cvc5_record_a_Int_b_Bool
Type 2: __cvc5_record_b_Bool_a_Int
-/
#guard_msgs in #eval Env.runIO do
  let ab ← srt
  let ba ← Srt.record #[("b", ← Srt.bool), ("a", ← Srt.int)]
  println! "same sort : {ab == ba}"
  let r ← Term.mkRecord ab #[("a", ← Term.mkInt 7), ("b", ← Term.mkBool true)]
  let r' ← Term.mkRecord ba #[("a", ← Term.mkInt 7), ("b", ← Term.mkBool true)]
  println! "mixed     : {← caught do pure s!"{← Term.equal r r'}"}"



/-! ## Through a solver

A record's fields come back out of a model, and an update is a real update.
-/

/-- info:
model a   : 7
model b   : true
updated a : 9
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let p ← s.declareConst "p" srt
  let seven ← Term.mkInt 7
  (← Term.equal (← p.recordGet "a") seven) |> s.assert
  (← p.recordGet "b") |> s.assert

  let a ← p.recordGet "a"
  let b ← p.recordGet "b"
  let updated ← (← p.recordSet "a" (← Term.mkInt 9)).recordGet "a"
  s.checkSat (ifSat := do
    println! "model a   : {← s.getValueAs (α := Int) a}"
    println! "model b   : {← s.getValueAs (α := Bool) b}"
    println! "updated a : {← s.getValueAs (α := Int) updated}")



/-! ## `Fields`: a record's fields, by name

The field names are in the *type*, which is what makes reading one total — `fs.get "a"` answers a
`Term`, not an `Option Term`. The index comes from the spine, so it is never written out.
-/

/-- info:
fields  : {a := 7, b := true}
a       : 7
b       : true
terms   : #[7, true]
after set: {a := 9, b := true}
-/
#guard_msgs in #eval Env.runIO do
  let fs ← do
    pure <| Fields.last "b" (← Term.mkBool true)
      |>.cons "a" (← Term.mkInt 7)
  println! "fields  : {fs}"
  println! "a       : {fs.get "a"}"
  println! "b       : {fs.get "b"}"
  println! "terms   : {fs.terms}"
  let fs := fs.set "a" (← Term.mkInt 9)
  println! "after set: {fs}"

/-! A name that is not a field has no `FieldAt` instance, so it does not compile. -/

/--
error: failed to synthesize instance of type class
  FieldAt ["a", "b"] "c"

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Ω] (fs : Fields ["a", "b"]) : Term := fs.get "c"

/-! A name occurring twice resolves to the first — matching what `Srt.record` reports, though such
a record has no sort at all. -/

/-- info:
first wins : 7
-/
#guard_msgs in #eval Env.runIO do
  let fs ← do
    pure <| Fields.last "a" (← Term.mkBool true)
      |>.cons "a" (← Term.mkInt 7)
  println! "first wins : {fs.get "a"}"

/-! ### Building from, and reading back into, a `Fields`

`mkRecordOf` is `mkRecord` given the pairs, so the names still have to agree with the sort — that
is a fact about the sort, which no index can state.
-/

/-- info:
record   : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
same     : true
read back: {a := (a (__cvc5_record_a_Int_b_Bool_ctor 7 true)), b := (b (__cvc5_record_a_Int_b_Bool_ctor 7 true))}
just a   : {a := (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))}
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  let fs ← do
    pure <| Fields.last "b" (← Term.mkBool true)
      |>.cons "a" (← Term.mkInt 7)
  let r ← Term.mkRecordOf srt fs
  println! "record   : {r}"
  println! "same     : {r == (← Term.mkRecord srt fs.pairs)}"

  -- and back out again
  let back ← r.recordFields ["a", "b"]
  println! "read back: {back}"
  println! "just a   : {← r.recordFields ["a"]}"

/-! The names given to `recordFields` are checked, since they are not read off the sort. -/

/-- info:
bad name : caught: record sort `__cvc5_record_a_Int_b_Bool` has no field named `c`, its fields are `a`, `b`
-/
#guard_msgs in #eval Env.runIO do
  let srt ← srt
  let r ← Term.mkRecord srt #[("a", ← Term.mkInt 7), ("b", ← Term.mkBool true)]
  println! "bad name : {← caught do pure s!"{← r.recordFields ["a", "c"]}"}"


/-! # The `smt!` DSL's record forms

`{a := t}`, `{r with a := t}`, `r.a` and `e |>.a` are declared and expanded in this theory's own
module, so they exist exactly where records do — importing another theory alone leaves them out of
the grammar. Their tests belong here for the same reason.
-/

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
