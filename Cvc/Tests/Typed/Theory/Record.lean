/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Record
import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Solver

public meta import Cvc.Typed.Theory.Record
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Solver



/-! # Records, typed -/
namespace Cvc.Tests.Typed.Record

open Cvc Typed

/-- `{a : Int, b : Bool}`, as an index. -/
abbrev P := Record [("a", Int), ("b", Bool)]

/-- Catches a user error, so a rejection can be printed rather than propagated. -/
def caught [Ω] (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"

/-- The fields of a `P`. -/
def fields [Ω] : Env (Fields [("a", Int), ("b", Bool)]) := do
  return Fields.last "b" (← Term.mkBool true)
    |>.cons "a" (← Term.mkInt 7)



/-! ## The index carries the names and the types

A field's term comes back at the type the index gives it, so it is an operand of that type's
operators with nothing to re-type — which is the whole point of the index.
-/

/-- info: fields  : {a := 7, b := true}
a       : 7
b       : true
a + 1   : (+ 7 1)
¬ b     : (not true)
set     : {a := 9, b := true}
-/
#guard_msgs in #eval Env.runIO do
  let fs ← fields
  println! "fields  : {fs}"
  let a : Term Int := fs.get "a"
  let b : Term Bool := fs.get "b"
  println! "a       : {a}"
  println! "b       : {b}"
  -- `a` is arithmetic, with no ascription anywhere
  println! "a + 1   : {← Term.add (fs.get "a") (← Term.mkInt 1)}"
  println! "¬ b     : {← Term.not (fs.get "b")}"
  println! "set     : {fs.set "a" (← Term.mkInt 9)}"

section signatures
variable [Ω] (fs : Fields [("a", Int), ("b", Bool)]) (r : Term P)

/-- A field's term has the field's type. -/
example : Term Int := fs.get "a"
/-- And so does one read off a record term. -/
example : Env (Term Bool) := r.recordGet "b"
/-- An update answers the record, not a field. -/
example : Env (Term P) := do r.recordSet "a" (← Term.mkInt 9)
/-- Reading a record apart answers its fields, at the index's types. -/
example : Env (Fields [("a", Int), ("b", Bool)]) := r.recordFields

end signatures



/-! ## What does not compile

Each of these is a runtime error sort-erased. The field list is written once, in the spine, so
every one of them is caught where it is written rather than where the term is built.
-/

/--
error: failed to synthesize instance of type class
  FieldOf [("a", Int), ("b", Bool)] "c" Int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Ω] (fs : Fields [("a", Int), ("b", Bool)]) : Term Int := fs.get "c"

/--
error: failed to synthesize instance of type class
  FieldOf [("a", Int), ("b", Bool)] "a" Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Ω] (fs : Fields [("a", Int), ("b", Bool)]) : Term Bool := fs.get "a"

/-! Fields in the wrong order are a different index, and so is one omitted. Sort-erased these are
`[internal] bad type for constructor argument` and `number of arguments does not match` out of
cvc5, naming the mono-morphised datatype. -/

/--
error: Type mismatch
  Fields.cons "a" __do_lift✝¹ (Fields.last "b" __do_lift✝)
has type
  Fields [("a", Int), ("b", Bool)]
but is expected to have type
  Fields [("b", Bool), ("a", Int)]
-/
#guard_msgs in
example [Ω] : Env (Fields [("b", Bool), ("a", Int)]) := do
  return Fields.cons "a" (← Term.mkInt 7) (Fields.last "b" (← Term.mkBool true))

/--
error: Type mismatch
  Fields.last "a" __do_lift✝
has type
  Fields [("a", Int)]
but is expected to have type
  Fields [("a", Int), ("b", Bool)]
-/
#guard_msgs in
example [Ω] : Env (Fields [("a", Int), ("b", Bool)]) := do
  return Fields.last "a" (← Term.mkInt 7)



/-! ## Building, and taking apart

`mkRecord` takes neither a sort nor field names: the index has both.
-/

/-- info: record   : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
sort     : __cvc5_record_a_Int_b_Bool
a        : (a (__cvc5_record_a_Int_b_Bool_ctor 7 true))
set a    : ((_ update a) (__cvc5_record_a_Int_b_Bool_ctor 7 true) 9)
all      : {a := (a (__cvc5_record_a_Int_b_Bool_ctor 7 true)), b := (b (__cvc5_record_a_Int_b_Bool_ctor 7 true))}
-/
#guard_msgs in #eval Env.runIO do
  let r ← Term.mkRecord (← fields)
  println! "record   : {r}"
  println! "sort     : {← Srt.of P}"
  println! "a        : {← r.recordGet "a"}"
  println! "set a    : {← r.recordSet "a" (← Term.mkInt 9)}"
  println! "all      : {← r.recordFields}"

/-! A record may be a field of a record, and nests as an index does. -/

/-- info: nested   : __cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int
inner a  : (a (inner (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)))
-/
#guard_msgs in #eval Env.runIO do
  let inner ← Term.mkRecord (← fields)
  let outer ← Term.mkRecord <| Fields.last "tag" (← Term.mkInt 1)
    |>.cons "inner" inner
  println! "nested   : {← Srt.of (Record [("inner", P), ("tag", Int)])}"
  println! "inner a  : {← (← outer.recordGet "inner").recordGet "a"}"



/-! ## Through a solver -/

/-- info: model a   : 7
model b   : true
updated a : 9
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let p ← s.declareConst P "p"
  (← Term.equal (← p.recordGet "a") (← Term.mkInt 7)) |> s.assert
  (← p.recordGet "b") |> s.assert

  let a ← p.recordGet "a"
  let b ← p.recordGet "b"
  let updated ← (← p.recordSet "a" (← Term.mkInt 9)).recordGet "a"
  s.checkSat (ifSat := do
    println! "model a   : {← s.getValue a}"
    println! "model b   : {← s.getValue b}"
    println! "updated a : {← s.getValue updated}")



/-! ## Lean values

`Record fields` is the value a record-sorted term denotes as well as its index, so `mkValue` and
`getValue` work on it like any other sort — and `Solver.getValue` answers a whole record rather
than one field at a time.
-/

/-- `{a := 7, b := true}`, as a value. -/
def value : Record [("a", Int), ("b", Bool)] :=
  Record.last "b" true |>.cons "a" 7

/-- info: value    : {a := 7, b := true}
a        : 7
b        : true
set a    : {a := 9, b := true}
a + 1    : 8
-/
#guard_msgs in #eval Env.runIO do
  println! "value    : {value}"
  println! "a        : {value.get "a"}"
  println! "b        : {value.get "b"}"
  println! "set a    : {value.set "a" 9}"
  -- the field's Lean type, so ordinary Lean arithmetic
  println! "a + 1    : {value.get "a" + 1}"

section signatures
/-- A field's value has the field's Lean type. -/
example : Int := value.get "a"
/-- And an update answers the record. -/
example : Record [("a", Int), ("b", Bool)] := value.set "b" false
end signatures

/-! Both directions of the conversion, and the round trip. -/

/-- info: term     : (__cvc5_record_a_Int_b_Bool_ctor 7 true)
round trip: {a := 7, b := true}
same     : true
-/
#guard_msgs in #eval Env.runIO do
  let term ← Term.mkValue value
  println! "term     : {term}"
  println! "round trip: {← term.extractValue}"
  println! "same     : {(← term.extractValue) == value}"

/-! The reader walks the constructor's arguments, so it works on a term that was *built* — sets and
sequences need a model's answer, records do not. -/

/-- info: built    : {a := 7, b := true}
not a value: caught: `p` is not a record value
-/
#guard_msgs in #eval Env.runIO do
  let built ← Term.mkRecord (← fields)
  println! "built    : {← built.extractValue}"
  let p ← (← Solver.new).declareConst P "p"
  println! "not a value: {← caught do pure s!"{← p.extractValue}"}"

/-! And out of a model, in one go rather than field by field. -/

/-- info: model    : {a := 7, b := true}
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let p ← s.declareConst P "p"
  (← Term.equal (← p.recordGet "a") (← Term.mkInt 7)) |> s.assert
  (← p.recordGet "b") |> s.assert
  s.checkSat (ifSat := do println! "model    : {← s.getValue p}")

/-! A record nests, as a value and as a sort: its fields' instances are what it asks for, and only
where it is asked for them. -/

/-- info: nested   : {inner := {a := 7, b := true}, tag := 1}
inner a  : 7
term     : (__cvc5_record_inner___cvc5_record_a_Int_b_Bool_tag_Int_ctor (__cvc5_record_a_Int_b_Bool_ctor 7 true) 1)
back     : {inner := {a := 7, b := true}, tag := 1}
ordered  : true
-/
#guard_msgs in #eval Env.runIO do
  let nested : Record [("inner", Record [("a", Int), ("b", Bool)]), ("tag", Int)] :=
    Record.last "tag" 1 |>.cons "inner" value
  println! "nested   : {nested}"
  println! "inner a  : {(nested.get "inner").get "a"}"
  let term ← Term.mkValue nested
  println! "term     : {term}"
  println! "back     : {← term.extractValue}"
  -- ordered, so a set of records can be spelled *and* built
  println! "ordered  : {compare value (value.set "a" 8) == Ordering.lt}"


/-! # The `smt!` DSL's record forms

`{a := t}`, `{r with a := t}`, `r.a` and `e |>.a` are declared and expanded in this theory's own
module, so they exist exactly where records do — importing another theory alone leaves them out of
the grammar. Their tests belong here for the same reason.
-/

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
