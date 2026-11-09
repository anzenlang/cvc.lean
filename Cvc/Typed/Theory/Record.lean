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
-- the sort-erased spine's constructor is private, and `Fields.toUntyped` builds one
import all Cvc.Untyped.Theory.Record

public import Cvc.Srt
public import Cvc.Types.Record
public import Cvc.Untyped.Theory.Record
public meta import Cvc.Ext
public import Cvc.Typed.Core.Value



/-! # Records, typed

A record with fields `a : Int` and `b : Bool` is a `Term (Record [("a", Int), ("b", Bool)])`. Its
field names, their order and their types are part of the index, so a missing field, a field out of
order, an unknown name or a field at the wrong type does not compile.

```lean
Term.mkRecord (.cons "a" x (.last "b" y))   -- `x : Term Int`, `y : Term Bool`
smt! {a := x, b := y}                       -- the same record
smt! {r with a := 9}                        -- `r`, its field `a` replaced
smt! r.a                                    -- `r`'s field `a`; also `e |>.a`
```

A field of a literal may state its sort, `{a : Int := 7}`, which is then checked. A record has at
least one field.
-/
-- `Fields` holds its terms erased, with the types only in the index, and `FieldOf` carries a
-- position rather than a projection: a list binding one type variable per field would land in
-- `Type 1`, and `Env` answers only `Type`.
namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Term → T



/-! ## A record's fields, by name -/

/-- One term per field, the field names and types in the index.

Built with `last` and `cons`: `.cons "a" x (.last "b" y)`.
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

/-- A field's term, at the type the index gives it; a name that is not a field does not compile. -/
def get (name : String) [F : FieldOf fields name gamma] : Term gamma := fs.values[F.idx]

/-- The same fields, with one field's term replaced. -/
def set (name : String) [F : FieldOf fields name gamma] (value : Term gamma) : Fields fields :=
  ⟨fs.values.set F.idx value.erase⟩

/-- The terms, sort-erased, in the order the fields are. -/
def terms : Untyped.Terms := fs.values.toArray

/-- The fields as name/term pairs, sort-erased, in the order the fields are. -/
def pairs : Array (String × Untyped.Term) := (fields.map Prod.fst).toArray.zip fs.terms

/-- The sort-erased fields, their names read off the index; free. -/
def toUntyped : Untyped.Fields (fields.map Prod.fst) := ⟨fs.values.cast (by simp)⟩

@[inherit_doc toUntyped]
abbrev erase : Untyped.Fields (fields.map Prod.fst) := fs.toUntyped

instance : ToString (Fields fields) where
  toString fs :=
    let fields := fs.pairs.toList.map fun (n, t) => s!"{n} := {t}"
    "{" ++ ", ".intercalate fields ++ "}"

end Fields

/-- Types sort-erased fields at `fields`, checking each field's term against its type's sort.

The field names must be `fields`' names, a proof `rfl` finds when both are written out. `toTyped`
infers `fields` from the expected type; `typeCheckAs` and `typeCheck` are the same two functions.
-/
def _root_.Cvc.Untyped.Fields.toTypedAs (fields : List (String × Type)) [Fs : ToTypFields fields]
  (fs : Untyped.Fields names)
  (_sameNames : names = fields.map Prod.fst := by
    first | rfl | fail "failed to prove the field names are the ones the index gives")
: Env (Fields fields) := do
  let want ← Typ.toSrtFields Fs.typs
  let terms := fs.terms
  for h : idx in [0 : terms.size] do
    let actual ← terms[idx].getSort
    let some (name, w) := want[idx]?
      | throwInternal "a record's terms and its field sorts disagree in number"
    if actual != w then
      throwUser s!"cannot type field `{name}` at `{w}`, its term has sort `{actual}`"
  return ⟨fs.values.cast (by subst _sameNames; simp)⟩

@[inherit_doc Untyped.Fields.toTypedAs]
def _root_.Cvc.Untyped.Fields.toTyped [ToTypFields fields] (fs : Untyped.Fields names)
  (_sameNames : names = fields.map Prod.fst := by
    first | rfl | fail "failed to prove the field names are the ones the index gives")
: Env (Fields fields) := fs.toTypedAs fields _sameNames

@[inherit_doc Untyped.Fields.toTypedAs]
abbrev _root_.Cvc.Untyped.Fields.typeCheckAs := @Untyped.Fields.toTypedAs

@[inherit_doc Untyped.Fields.toTypedAs]
abbrev _root_.Cvc.Untyped.Fields.typeCheck := @Untyped.Fields.toTyped



/-! ## Records and their fields -/

namespace Term

/-- Builds a record value from its fields: `mkRecord (.cons "a" x (.last "b" y))`. -/
def mkRecord [ToTypFields fields] (fs : Fields fields) : Env (Term (Record fields)) := do
  T.mkRecord (← Srt.of (Record fields)) fs.pairs

/-- Answers `term` unchanged, failing unless `expected` is its sort. -/
def checkFieldSrt [ToTyp gamma] (field : String) (expected : Srt) (term : Term gamma)
: Env (Term gamma) := do
  let actual ← Srt.of gamma
  unless actual == expected do
    throwUser s!"field `{field}` is stated at sort `{expected}`, but its term has sort `{actual}`"
  return term
-- What a record literal's optional sort annotation expands to. The index already fixes the sort, so
-- an annotation can only confirm it — which is worth doing, since a reader of the literal takes it
-- on trust.

/-- Reads a field out of a record value. -/
def recordGet (record : Term (Record fields)) (name : String) [FieldOf fields name gamma]
: Env (Term gamma) :=
  T.recordGet record.erase name

/-- The record value with one field replaced. -/
def recordSet (record : Term (Record fields)) (name : String) [FieldOf fields name gamma]
(value : Term gamma) : Env (Term (Record fields)) :=
  T.recordSet record.erase name value.erase

/-- Reads a record value apart, into all of its fields. -/
def recordFields (record : Term (Record fields)) : Env (Fields fields) :=
  go fields
where
  /-- Collects the fields of `remaining`, in order. -/
  go : (remaining : List (String × Type)) → Env (Fields remaining)
    | [] => return .nil
    | (name, _) :: rest => do
      return Fields.cons name (← T.recordGet record.erase name) (← go rest)

/-- A record literal's fields, `none` if the term is not a literal.

A declared constant, an update or an `ite` is not a literal. `fs.get "a"` then reads a field.
-/
def recordFields? (t : Term (Record fields)) : Env (Option (Fields fields)) := do
  let raw := t.erase
  unless raw.getKind? == some .APPLY_CONSTRUCTOR do return none
  -- the first kid is the constructor
  let args := raw.getKids.extract 1
  if h : args.size = fields.length then return some ⟨⟨args, h⟩⟩
  throwInternal s!"`{raw}`: {args.size} fields for a record of {fields.length}"

end Term



/-! ## Values

`Record fields` is also the Lean value a record term denotes, so `Solver.getValue` answers one. It
converts field by field, so a record needs of its fields only the conversions asked of it. Reading
works on a built record literal as well as on a model's answer.
-/
-- The reader walks the term's children, not its selectors: a record value is an
-- `APPLY_CONSTRUCTOR` whose first child is the constructor and whose others are the fields in
-- order.

/-- Reads a record's fields off the arguments of its constructor application. -/
class TermToValues (fields : List (String × Type)) where
  /-- Reads one value per field, in order. -/
  ofTerms : [Ω] → List Untyped.Term → Env (Values fields)

/-- A sort-erased term at any index, unchecked: the caller vouches for its sort. -/
protected def ofErased (term : Untyped.Term) : Term gamma := term
-- a declaration rather than a cast at its use, which an instance body could not unfold

/-- The record term of a list of field terms, in the sort's order. -/
def mkRecordOfTerms [ToTypFields fields] (terms : List Untyped.Term)
: Env (Term (Record fields)) := do
  T.mkRecord (← Srt.of (Record fields)) ((fields.map Prod.fst).toArray.zip terms.toArray)

instance : TermToValues [] := ⟨fun _ => return ⟨⟩⟩

instance [A : TermToValue gamma] [R : TermToValues fields]
: TermToValues ((name, gamma) :: fields) where
  ofTerms
    | [] => throwUser s!"record value has no argument for field `{name}`"
    | term :: terms => do return (← A.termToValue (Typed.ofErased term), ← R.ofTerms terms)

/-- Builds the term of each of a record's field values. -/
class ValuesToTerm (fields : List (String × Type)) where
  /-- Builds one term per field, in order. -/
  toTerms : [Ω] → Values fields → Env (List Untyped.Term)

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



public meta section

open Lean

-- The record forms of `smt!`, shown in the module doc. The syntax is declared once, beside the
-- sort-erased constructors; this layer adds only its own expansion, tried first and declining
-- anything that is not this layer.

/-- Resolves a dotted identifier of the typed layer into a head and the fields read off it. -/
syntax (name := smtProjT) "smtProjT% " ident : term

-- The DSL's machinery lives in `Cvc.Ext`, never in `Cvc`, so that it cannot clash with the API a
-- user opens.
namespace Ext

open Cvc.Ext

/-- Elaborates a typed identifier, reading off whatever fields it names. -/
@[term_elab smtProjT] def elabSmtProjT : Lean.Elab.Term.TermElab := fun stx expected? => do
  let `(smtProjT% $id) := stx | Lean.Elab.throwUnsupportedSyntax
  elabSmtProj .typed id expected?

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.typed do Macro.throwUnsupported
    let stx := t.raw
    match stx.getKind with
    | ``smtIdent =>
      let id : Ident := ⟨stx[0]⟩
      if id.getId == `true || id.getId == `false then Macro.throwUnsupported
      `(smtProjT% $id)
    | ``smtProj | ``smtPipeProj =>
      let head ← deferSmt layer stx[0]
      let field := Syntax.mkStrLit stx[2].getId.toString
      bindArgs #[head] fun ids => `($(layer.op `recordGet) $(ids[0]!) $field)
    | ``smtRecord =>
      let fields := stx[1].getSepArgs
      let names := fields.map fun field => Syntax.mkStrLit (recFieldName field)
      let terms ← fields.mapM fun field => deferSmt layer (recFieldTerm field)
      -- the index carries every field's sort, so a stated one is checked against it and the spine
      -- is what says which record this is
      let checked ← fields.mapIdxM fun i field =>
        match recFieldSrt? field with
        | some srt =>
          let check := layer.op `checkFieldSrt
          `($(terms[i]!) >>= fun v => srtOf% ($srt) >>= fun srt => $check $(names[i]!) srt v)
        | Option.none => pure terms[i]!
      bindArgs checked fun ids => do
        let last := ids.size - 1
        let mut spine ← `($(layer.name `Fields.last) $(names[last]!) $(ids[last]!))
        for i in [0 : last] do
          let j := last - 1 - i
          spine ← `($(layer.name `Fields.cons) $(names[j]!) $(ids[j]!) $spine)
        `($(layer.op `mkRecord) $spine)
    | ``smtWith =>
      let fields := stx[3].getSepArgs
      recCheckDistinct fields
      let names := fields.map fun field => Syntax.mkStrLit (recFieldName field)
      let record ← deferSmt layer stx[1]
      let values ← fields.mapIdxM fun i field => do
        let value ← deferSmt layer (recFieldTerm field)
        match recFieldSrt? field with
        | some srt =>
          let check := layer.op `checkFieldSrt
          `($value >>= fun v => srtOf% ($srt) >>= fun srt => $check $(names[i]!) srt v)
        | Option.none => pure value
      recUpdate layer names values record
    | _ => Macro.throwUnsupported

end Ext

end
