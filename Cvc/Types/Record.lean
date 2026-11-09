/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt



/-! # Records

`Record fields` is both the index of a record-sorted term and the Lean value such a term denotes,
`fields` being its named fields in order. **The order is part of the sort**: `{a : Int, b : Bool}`
and `{b : Bool, a : Int}` are different sorts.

```lean
def origin : Record [("x", Int), ("y", Int)] := .cons "x" 0 (.last "y" 0)
#eval origin.get "y"   -- 0
```
-/
-- A record sort is structural, unlike every other datatype: cvc5 builds the same sort from the same
-- fields, so `Typ.record` rebuilds it on demand and `Record fields` denotes one sort wherever it is
-- written. That is also why the index is a field list rather than a Lean structure: a `structure
-- Point` would be nominal, so two identical structures would denote one SMT sort while being
-- different indices, and `Srt.toTyp` could not say which one a sort came from.
namespace Cvc public section



/-- The `Typ`s a list of named Lean types denotes. -/
class ToTypFields (fields : List (String × Type)) where
  /-- The fields, in order, at their `Typ`s. -/
  typs : List (String × Typ)

namespace ToTypFields

instance : ToTypFields [] := ⟨[]⟩

instance [A : ToTyp α] [Fs : ToTypFields fields] : ToTypFields ((name, α) :: fields) :=
  ⟨(name, A.typ) :: Fs.typs⟩

end ToTypFields



/-- A record's field values: `gamma` for each field, in order, as nested pairs ending in `PUnit`. -/
@[expose] def Values : List (String × Type) → Type
  | [] => PUnit
  | (_name, gamma) :: rest => gamma × Values rest
-- A **computed** product rather than a spine, and that is what keeps it in `Type`. An inductive
-- collecting one value per field would have to bind a type variable per constructor and would land
-- in `Type 1`, which `Env` cannot answer — so `Solver.getValue` could never produce one.
--
-- `expose`d because every instance below reduces it: a downstream module has to see that a
-- record's values *are* a product to lift `Ord` or `ToString` over them.

/-- A record of the named, ordered `fields`: a record sort, and a value of it. -/
structure Record (fields : List (String × Type)) where
  /-- The field values, in order. -/
  values : Values fields

namespace Record

/-- A record's last field, and its value. -/
def last (_name : String) (value : gamma) : Record [(_name, gamma)] := ⟨(value, ⟨⟩)⟩
-- There is no empty record: `Srt.record` refuses one, so building starts from the last field.

/-- Adds a field's value in front of the ones collected so far. -/
def cons (_name : String) (value : gamma) (rest : Record fields)
: Record ((_name, gamma) :: fields) := ⟨(value, rest.values)⟩

end Record



/-- `name` is one of `fields`, with type `gamma`: where it sits, and how to reach it.

Resolved by instance search, so a name that is not a field, or one asked for at the wrong type,
does not compile.
-/
class FieldOf (fields : List (String × Type)) (name : String) (gamma : outParam Type) where
  /-- Where the field sits in `fields`. -/
  idx : Fin fields.length
  /-- The field's value. -/
  get : Values fields → gamma
  /-- The values, with this field's replaced. -/
  set : Values fields → gamma → Values fields
-- The two representations need different accessors. Terms are held erased in an array, and carrying
-- a position rather than a projection is what keeps a record of *terms* in `Type`, for the reason
-- `Values` is a computed product. `Values` is a nested product with nothing to index, so a value is
-- reached by projection.
--
-- The position is a `Fin`, which is safe here in a way a hand-written one would not be —
-- resolution produces it, so there is no numeral for `Fin`'s modular `OfNat` to reduce.
--
-- Where a field name occurs twice the head match wins, matching `Srt.record`'s "first duplicate"
-- report — but such an index has no sort at all, `Srt.record` refusing duplicate names.

instance (priority := high) : FieldOf ((name, gamma) :: fields) name gamma where
  idx := 0
  get vs := vs.fst
  set vs v := (v, vs.snd)

instance [F : FieldOf fields name gamma] : FieldOf ((_other, _beta) :: fields) name gamma where
  idx := F.idx.succ
  get vs := F.get vs.snd
  set vs v := (vs.fst, F.set vs.snd v)

namespace Record variable (r : Record fields)

/-- A field's value.

Total: a name that is not a field has no `FieldOf` instance, so there is no `none` to answer.
-/
def get (name : String) [F : FieldOf fields name gamma] : gamma := F.get r.values

/-- The same record, with one field's value replaced. -/
def set (name : String) [F : FieldOf fields name gamma] (value : gamma) : Record fields :=
  ⟨F.set r.values value⟩

end Record



/-! ### Instances for nesting

A record's order, equality, hash and string form are lifted field by field, each through its own
class, so a record demands of its fields only what is asked of the record.
-/

/-- Lifts `Ord` over a record's fields, lexicographically. -/
class OrdFields (fields : List (String × Type)) where
  /-- Compares two records' values. -/
  compare : Values fields → Values fields → Ordering

instance : OrdFields [] := ⟨fun _ _ => .eq⟩

instance [Ord gamma] [R : OrdFields fields] : OrdFields ((_name, gamma) :: fields) :=
  ⟨fun (a, as) (b, bs) => match Ord.compare a b with | .eq => R.compare as bs | o => o⟩

/-- Lifts `DecidableEq` over a record's fields. -/
class DecidableEqFields (fields : List (String × Type)) where
  /-- Decides equality of two records' values. -/
  decEq : DecidableEq (Values fields)

instance : DecidableEqFields [] := ⟨fun _ _ => isTrue rfl⟩

instance [DecidableEq gamma] [R : DecidableEqFields fields]
: DecidableEqFields ((_name, gamma) :: fields) :=
  ⟨have := R.decEq; inferInstanceAs (DecidableEq (gamma × Values fields))⟩

/-- Lifts `Hashable` over a record's fields. -/
class HashableFields (fields : List (String × Type)) where
  /-- Hashes a record's values. -/
  hash : Values fields → UInt64

instance : HashableFields [] := ⟨fun _ => 0⟩

instance [Hashable gamma] [R : HashableFields fields] : HashableFields ((_name, gamma) :: fields) :=
  ⟨fun (v, vs) => mixHash (Hashable.hash v) (R.hash vs)⟩

/-- Lifts `ToString` over a record's fields, and names them. -/
class ToStringFields (fields : List (String × Type)) where
  /-- One `name := value` per field, in order. -/
  strings : Values fields → List String

instance : ToStringFields [] := ⟨fun _ => []⟩

instance [ToString gamma] [R : ToStringFields fields] : ToStringFields ((name, gamma) :: fields) :=
  ⟨fun (v, vs) => s!"{name} := {v}" :: R.strings vs⟩

instance [O : OrdFields fields] : Ord (Record fields) := ⟨fun a b => O.compare a.values b.values⟩

instance [D : DecidableEqFields fields] : DecidableEq (Record fields) :=
  fun a b =>
    match D.decEq a.values b.values with
    | isTrue h => isTrue (congrArg Record.mk h)
    | isFalse h => isFalse fun eq => h (congrArg Record.values eq)

instance [H : HashableFields fields] : Hashable (Record fields) := ⟨fun r => H.hash r.values⟩

instance [S : ToStringFields fields] : ToString (Record fields) :=
  ⟨fun r => "{" ++ ", ".intercalate (S.strings r.values) ++ "}"⟩

instance [Fs : ToTypFields fields] : ToTyp (Record fields) := ⟨.record Fs.typs⟩
