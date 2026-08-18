/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs

public import Cvc.Srt
public import Cvc.Types.Record
public import Cvc.Untyped.Theory.Record
public import Cvc.Typed.Core.Value



/-! # Records, typed

`Record fields` is the index, so a record's field names *and* the type of each are static. That is
enough to make everything the sort-erased layer checks at runtime a type error instead, and it
leaves nothing to look up: unlike a declared datatype, whose constructors and field sorts are facts
about a runtime declaration, a record sort is structural, so there is no handle to carry and
`Datatype.Ctor`/`Field` have no counterpart here.

What the index does:

- the field list is written **once**, in the `Fields` spine, and inferred from there;
- fields in the wrong order, or one omitted, are a type error rather than a constructor arity or
  sort error out of cvc5;
- `recordGet` at a name that is not a field, or at the wrong type, does not resolve `FieldOf` and
  does not compile.

What stays a runtime fact is what a type here cannot state: that a *declared* sort matches, which
does not arise, records being structural. So nothing in this module can fail on a well-typed call.

`Fields` holds its terms **erased**, with the types only in the index, and `FieldOf` carries a
position rather than a projection. That is not an optimisation: a spine binding one type variable
per field would land in `Type 1`, and `Env` answers only `Type`.
-/
namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## A record's fields, by name -/

/-- One term per field, along with the fields they are.

`nil` and `cons` are the only ways to build one, and between them they keep the terms and the index
in step — so a record's fields cannot come out reordered, short, or at the wrong type.
-/
structure Fields (fields : List (String × Type)) where
  private mk ::
  private values : Vector Untyped.Term fields.length

namespace Fields variable (fs : Fields fields)

/-- A record has at least one field, so this is not public: `last` is where a spine starts.

It stays for the recursions that take a record apart, which have an empty case whatever the
records do.
-/
private def nil : Fields [] := ⟨#v[]⟩

/-- A record's last field. -/
def last (name : String) (value : Term gamma) : Fields [(name, gamma)] := ⟨#v[value.erase]⟩

/-- Adds a field in front of the ones collected so far. -/
def cons (name : String) (value : Term gamma) (rest : Fields fields)
: Fields ((name, gamma) :: fields) :=
  ⟨⟨#[value.erase] ++ rest.values.toArray, by simp; omega⟩⟩

/-- A field's term, at the type the index gives it.

Total: a name that is not a field has no `FieldOf` instance, so there is no `none` to answer.
-/
def get (name : String) [F : FieldOf fields name gamma] : Term gamma := fs.values[F.idx]

/-- The same fields, with one field's term replaced. -/
def set (name : String) [F : FieldOf fields name gamma] (value : Term gamma) : Fields fields :=
  ⟨fs.values.set F.idx value.erase⟩

/-- The terms, sort-erased, in the order the fields are. -/
def erase : Untyped.Terms := fs.values.toArray

/-- The fields as name/term pairs, sort-erased, in the order the fields are. -/
def pairs : Array (String × Untyped.Term) := (fields.map Prod.fst).toArray.zip fs.erase

instance : ToString (Fields fields) where
  toString fs :=
    let fields := fs.pairs.toList.map fun (n, t) => s!"{n} := {t}"
    "{" ++ ", ".intercalate fields ++ "}"

end Fields



/-! ## Records and their fields -/

namespace Term

/-- Builds a record value.

Takes no sort: the index says which record this is. It takes no field *names* either, the spine
carrying them, so the one confusion a record invites — its fields in the wrong order — is a type
error rather than something to check.
-/
def mkRecord [ToTypFields fields] (fs : Fields fields) : Env (Term (Record fields)) := do
  T.mkRecord (← Srt.of (Record fields)) fs.pairs

/-- Checks a field's term against a stated sort, and answers it unchanged.

What a record literal's optional sort annotation expands to. The index already fixes the sort, so
an annotation can only confirm it — which is worth doing, since a reader of the literal takes it on
trust.
-/
def checkFieldSrt [ToTyp gamma] (field : String) (expected : Srt) (term : Term gamma)
: Env (Term gamma) := do
  let actual ← Srt.of gamma
  unless actual == expected do
    throwUser s!"field `{field}` is stated at sort `{expected}`, but its term has sort `{actual}`"
  return term

/-- Reads a field out of a record value. -/
def recordGet (record : Term (Record fields)) (name : String) [FieldOf fields name gamma]
: Env (Term gamma) :=
  T.recordGet record.erase name

/-- The record value with one field replaced. -/
def recordSet (record : Term (Record fields)) (name : String) [FieldOf fields name gamma]
(value : Term gamma) : Env (Term (Record fields)) :=
  T.recordSet record.erase name value.erase

/-- Reads a record value apart, into all of its fields.

Needs no field names, unlike its sort-erased counterpart: they are what the index is.
-/
def recordFields (record : Term (Record fields)) : Env (Fields fields) :=
  go fields
where
  /-- Collects the fields of `remaining`, in order. -/
  go : (remaining : List (String × Type)) → Env (Fields remaining)
    | [] => return .nil
    | (name, _) :: rest => do
      return Fields.cons name (← T.recordGet record.erase name) (← go rest)

end Term



/-! ## Values

`Record fields` is the Lean value a record-sorted term denotes as well as its index, so
`Solver.getValue` answers one directly. Both directions are lifted field by field, each through its
own class, so a record demands of its fields only what is asked of the record.

The reader walks the term's **children**, not its selectors: a record value is an
`APPLY_CONSTRUCTOR` whose arguments are the fields in order. That is what makes it work on a term
that was *built* as well as on one a model answered, as bags and nullables do and sets and
sequences do not.
-/

/-- Reads a record's fields off the arguments of its constructor application. -/
class TermToValues (fields : List (String × Type)) where
  /-- Reads one value per field, in order. -/
  ofTerms : List Untyped.Term → Env (Values fields)

/-- A sort-erased term at the index its field gives it. -/
def ofErased (term : Untyped.Term) : Term gamma := term

/-- The record term of a list of field terms, in the sort's order. -/
def mkRecordOfTerms [ToTypFields fields] (terms : List Untyped.Term)
: Env (Term (Record fields)) := do
  T.mkRecord (← Srt.of (Record fields)) ((fields.map Prod.fst).toArray.zip terms.toArray)

instance : TermToValues [] := ⟨fun _ => return ⟨⟩⟩

instance [A : TermToValue gamma] [R : TermToValues fields]
: TermToValues ((name, gamma) :: fields) where
  ofTerms
    | [] => throwUser s!"record value has no argument for field `{name}`"
    | term :: terms => do return (← A.termToValue (ofErased term), ← R.ofTerms terms)

/-- Builds the term of each of a record's field values. -/
class ValuesToTerm (fields : List (String × Type)) where
  /-- Builds one term per field, in order. -/
  toTerms : Values fields → Env (List Untyped.Term)

instance : ValuesToTerm [] := ⟨fun _ => return []⟩

instance [A : ValueToTerm gamma] [R : ValuesToTerm fields]
: ValuesToTerm ((_name, gamma) :: fields) where
  toTerms | (value, values) => do
    return (← A.valueToTerm value).erase :: (← R.toTerms values)

instance [R : TermToValues fields] : TermToValue (Record fields) where
  termToValue record := do
    let term := record.erase
    unless term.getKind? = some .APPLY_CONSTRUCTOR do
      throwUser s!"`{term}` is not a record value"
    -- an `APPLY_CONSTRUCTOR`'s first child is the constructor, the fields follow it
    return ⟨← R.ofTerms (term.getKids.toList.drop 1)⟩

instance [ToTypFields fields] [R : ValuesToTerm fields] : ValueToTerm (Record fields) where
  valueToTerm record := do mkRecordOfTerms (← R.toTerms record.values)
