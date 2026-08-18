/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs

public import Cvc.Srt
public import Cvc.Untyped.Theory.Datatype



/-! # Records, sort-erased

A record is a datatype, and cvc5 says so: `Srt.record` mono-morphises its fields into a datatype of
one constructor and one selector per field, named `__cvc5_record_a_Int_b_Bool` for
`{a : Int, b : Bool}`. So everything here goes through `Datatype`, and a record value is an
ordinary `APPLY_CONSTRUCTOR` term.

What this module adds over reaching for the datatype directly is the three facts a record
guarantees, and the error messages that follow from them:

- there is exactly **one** constructor, so `Srt.recordCtor` discharges the index rather than
  leaving the caller an impossible branch to write;
- the constructor's name is cvc5's, not the user's, so it is never the way in — everything here is
  keyed on **field names**, which are;
- a field's sort is known from the sort, so `Term.mkRecord` checks its arguments itself. cvc5 would
  otherwise report a swapped pair as `[internal] bad type for constructor argument`, naming the
  mono-morphised sort rather than the field that is wrong.

**Field order is part of the sort**, so `Term.mkRecord` takes its fields *by name* and puts them in
the sort's order. Writing them in the wrong order is then not an error at all, which is the point:
the one way to get a record's fields confused is the one way that cannot happen here.

`Fields` is the Lean-side record of terms: field names in its *type*, one term per field. That is
what makes reading a field total — `fs.get "a"` answers a `Term`, never an `Option Term`, because a
name that is not there has no `FieldAt` instance and does not compile. Sort-erased the index is the
names alone: a term carries no Lean type here, so putting types in it would buy nothing and would
have to be written out at every construction.
-/
namespace Cvc public section variable [Ω]

open Untyped (Term Terms)



/-! ## Reflecting a record sort -/

namespace Srt

/-- The datatype behind a record sort. -/
private def recordDatatype (srt : Srt) : Env Datatype := do
  unless srt.isRecord do
    throwUser s!"expected a record sort, got `{srt}`"
  srt.getDatatype

/-- The single constructor of a record sort.

A record has exactly one, so unlike `Datatype.getCtor` this needs no index and cannot fail on one.
-/
def recordCtor (srt : Srt) : Env Datatype.Ctor := do
  (← srt.recordDatatype).getCtor 0

/-- A record sort's fields, in the order the sort fixes. -/
def recordFields (srt : Srt) : Env (Array (String × Srt)) := do
  let mut fields := #[]
  for sel in ← srt.recordCtor do
    fields := fields.push (← sel.getName, ← sel.getCodomainSort)
  return fields

/-- The selector for one field, and the sort that field has.

Fails naming the record's fields, where cvc5 fails naming its own mono-morphised datatype.
-/
private def recordSelector (srt : Srt) (field : String) : Env (Datatype.Selector × Srt) := do
  for sel in ← srt.recordCtor do
    if (← sel.getName) == field then
      return (sel, ← sel.getCodomainSort)
  let names ← srt.recordFields
  let names := ", ".intercalate (names.toList.map fun (n, _) => s!"`{n}`")
  throwUser s!"record sort `{srt}` has no field named `{field}`, its fields are {names}"

end Srt



/-! ## Building and taking apart records -/

namespace Untyped.Term

/-- The first name occurring twice in a list, if any. -/
private def firstDuplicate : List String → Option String
  | [] => none
  | hd :: tl => if tl.contains hd then some hd else firstDuplicate tl

/-- Builds a record value, its fields given by name.

The fields may be given in any order: they are put in the order the sort fixes, which is the order
cvc5's constructor wants. Every field must be given exactly once, at the sort the record declares
it with.
-/
def mkRecord (srt : Srt) (fields : Array (String × Term)) : Env Term := do
  let expected ← srt.recordFields

  if let some name := firstDuplicate (fields.toList.map Prod.fst) then
    throwUser s!"record `{srt}` given more than one value for field `{name}`"

  for (name, _) in fields do
    unless expected.any (fun (n, _) => n == name) do
      throwUser s!"record sort `{srt}` has no field named `{name}`"

  let mut args := #[]
  for (name, fieldSrt) in expected do
    let some (_, value) := fields.find? (fun (n, _) => n == name)
      | throwUser s!"record `{srt}` given no value for field `{name}`"
    let valueSrt ← value.getSort
    unless valueSrt == fieldSrt do
      throwUser s!"\
        field `{name}` of record `{srt}` has sort `{fieldSrt}`, \
        but `{value}` has sort `{valueSrt}`"
    args := args.push value

  (← srt.recordCtor).apply args

/-- Builds a record value whose fields may each state their sort, or leave it to their term.

A field that states its sort has that sort checked against its term's, by `Term.mkRecord`; one that
does not takes its term's own. This is what a record literal expands to, and the reason it is a
function rather than something the expansion inlines is that a record's sort has to be built before
any field can be checked against it.
-/
def mkRecordFrom (fields : Array (String × Option Srt × Term)) : Env Term := do
  let mut srts := #[]
  for (name, srt?, value) in fields do
    srts := srts.push (name, ← srt?.getDM value.getSort)
  Term.mkRecord (← Srt.record srts) (fields.map fun (name, _, value) => (name, value))

/-- Checks a term against a stated sort, and answers it unchanged.

What a record literal's or update's optional sort annotation expands to, where the sort is not what
builds the record — in an update the record already has one. The message matches the typed layer's,
which checks the same thing against the index instead.
-/
def checkFieldSrt (field : String) (expected : Srt) (term : Term) : Env Term := do
  let actual ← term.getSort
  unless actual == expected do
    throwUser s!"field `{field}` is stated at sort `{expected}`, but its term has sort `{actual}`"
  return term

/-- Reads a field out of a record value. -/
def recordGet (record : Term) (field : String) : Env Term := do
  let (sel, _) ← (← record.getSort).recordSelector field
  sel.apply record

/-- The record value with one field replaced.

The replacement must have the sort the record declares that field with.
-/
def recordSet (record : Term) (field : String) (value : Term) : Env Term := do
  let srt ← record.getSort
  let (sel, fieldSrt) ← srt.recordSelector field
  let valueSrt ← value.getSort
  unless valueSrt == fieldSrt do
    throwUser s!"\
      field `{field}` of record `{srt}` has sort `{fieldSrt}`, \
      but `{value}` has sort `{valueSrt}`"
  sel.applyUpdate record value

end Untyped.Term



/-! ## A record's fields, by name

`Fields names` is one term per field, with the names in the type. It is the argument
`Term.mkRecord` really wants, and what reading a record term apart answers.
-/

namespace Untyped

/-- One term per field, the field names being `names`.

The terms are held in the order the names are, which is the order a record sort's constructor
wants, so `pairs` and `terms` hand `Term.mkRecord` what it takes with no rearranging.
-/
structure Fields [Ω] (names : List String) where
  private mk ::
  private values : Vector Term names.length

/-- `name` is one of `names`, and where it sits.

Carrying the *position* rather than a projection is what keeps `Fields` in `Type`: a spine binding
one type variable per field would land in `Type 1`, which nothing in `Env` can answer.

The position is a `Fin`, which is safe here in a way it would not be for a hand-written one:
resolution produces it, so there is no numeral for `Fin`'s modular `OfNat` to reduce.
-/
class FieldAt (names : List String) (name : String) where
  /-- Where the field sits in `names`. -/
  idx : Fin names.length

instance (priority := high) : FieldAt (name :: rest) name := ⟨0⟩

instance [F : FieldAt rest name] : FieldAt (other :: rest) name := ⟨F.idx.succ⟩

namespace Fields variable [Ω] (fs : Fields names)

/-- A record has at least one field, so this is not public: `last` is where a spine starts.

It stays for the recursions that take a record apart, which have an empty case whatever the
records do.
-/
private def nil : Fields [] := ⟨#v[]⟩

/-- A record's last field. -/
def last (name : String) (value : Term) : Fields [name] := ⟨#v[value]⟩

/-- Adds a field in front of the ones collected so far. -/
def cons (name : String) (value : Term) (rest : Fields names) : Fields (name :: names) :=
  ⟨⟨#[value] ++ rest.values.toArray, by simp; omega⟩⟩

/-- A field's term.

Total: a name that is not a field has no `FieldAt` instance, so there is no `none` to answer.
-/
def get (name : String) [F : FieldAt names name] : Term := fs.values[F.idx]

/-- The same fields, with one field's term replaced. -/
def set (name : String) [F : FieldAt names name] (value : Term) : Fields names :=
  ⟨fs.values.set F.idx value⟩

/-- The terms, in the order the names are. -/
def terms : Terms := fs.values.toArray

/-- The fields as name/term pairs, in the order the names are. -/
def pairs : Array (String × Term) := names.toArray.zip fs.terms

instance : ToString (Fields names) where
  toString fs :=
    let fields := fs.pairs.toList.map fun (n, t) => s!"{n} := {t}"
    "{" ++ ", ".intercalate fields ++ "}"

end Fields

end Untyped



/-! ## Records and their fields -/

namespace Untyped.Term

/-- Builds a record value from a `Fields`.

The names still have to agree with the sort, which is a runtime fact about the sort rather than
anything the index can say, so this is `Term.mkRecord` with the pairs handed to it.
-/
def mkRecordOf (srt : Srt) (fields : Fields names) : Env Term :=
  Term.mkRecord srt fields.pairs

/-- Reads a record value apart, into the fields named.

The names are given rather than read off the sort, since they are what the result's type is. Each
is checked as `Term.recordGet` checks it.
-/
def recordFields (record : Term) : (names : List String) → Env (Fields names)
  | [] => return .nil
  | name :: rest => return .cons name (← record.recordGet name) (← record.recordFields rest)

end Untyped.Term
