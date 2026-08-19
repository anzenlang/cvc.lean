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
public meta import Cvc.Ext



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



public meta section

open Lean

/-! ### Records

`{a : intSrt := 7, b : boolSrt := tru}` builds a record, and is Lean's own structure-instance
syntax with one difference that has to be stated loudly: **the order of the fields is part of the
sort**. `{a : … , b : …}` and `{b : … , a : …}` denote *different* record sorts, whose terms cvc5
refuses to mix, where Lean's structure instances are order-insensitive.

A field's sort may be **stated or left out**, per field, in either layer. Left out it is inferred:
sort-erased from the field term's own sort, typed from the index its term carries. Stated it is
*checked* against that same thing before the record is built, so an annotation can only confirm
what is there, never change it. The sort is an ordinary Lean term of type `Srt`, so the idiom is to
bind the sorts first and name them here.

There is **no syntax for the empty record**: `Srt.record` refuses one, the empty record denoting
what the empty tuple already denotes.
-/

/-- One field of a record literal: its name, its term, and optionally its sort. -/
declare_syntax_cat smtRecField (behavior := symbol)
/-- A field at a stated sort, `a : intSrt := 7`. -/
syntax (name := smtRecFieldOf) ident " : " term " := " smtTerm : smtRecField
/-- A field whose sort is inferred, `a := 7`. -/
syntax (name := smtRecField) ident " := " smtTerm : smtRecField

/-- A record literal, `{a := 7, b : boolSrt := tru}`. -/
syntax:max (name := smtRecord) "{" smtRecField,+ "}" : smtTerm

/-- A record update, `{r with a := 7}`.

Every field named must be one the record has, and no field may be named twice — checked as the
literal is expanded, so a repeated field is reported where it is written rather than silently
overwriting.
-/
syntax:max (name := smtWith) "{" smtTerm " with " smtRecField,+ "}" : smtTerm

/-- A field read off a term that is not an identifier, `(f x).a`.

An *identifier* head cannot come here: `r.a` is one token to the lexer, so it arrives as an
identifier and is taken apart by `smtProjU%`/`smtProjT%` instead. `smt! r .a`, with a space, is
neither and does not parse.
-/
syntax:max (name := smtProj) smtTerm:max noWs "." noWs ident : smtTerm

/-- A field read off whatever is to the left, `f x |>.a`.

Lean's `pipeProj`, at Lean's precedence — **minimum**, so it takes everything to its left:
`a + b |>.c` is `(a + b).c`, not `a + (b.c)`. That reading is nearly always a mistake here, an
arithmetic term having no fields, but it is a loud one and matching the language is worth more than
optimising for it.
-/
syntax:min (name := smtPipeProj) smtTerm " |>." noWs ident : smtTerm

/-- Resolves a dotted identifier of the sort-erased layer into a head and the fields read off it. -/
syntax (name := smtProjU) "smtProjU% " ident : term



/-! The DSL's machinery for these forms lives in `Cvc.Ext`, never in `Cvc`, so that it cannot clash
with the API a user opens.
-/
namespace Ext

/-- A record field's name. -/
def recFieldName (field : Syntax) : String := field[0].getId.toString

/-- A record field's stated sort, if it states one. -/
def recFieldSrt? (field : Syntax) : Option (TSyntax `term) :=
  if field.getKind == ``smtRecFieldOf then some ⟨field[2]⟩ else Option.none

/-- Refuses a record update naming one field twice, which would silently overwrite. -/
def recCheckDistinct (fields : Array Syntax) : MacroM Unit := do
  let mut seen : Array String := #[]
  for field in fields do
    let name := recFieldName field
    if seen.contains name then
      Macro.throwErrorAt field s!"record update names field `{name}` more than once"
    seen := seen.push name

/-- The `recordSet` chain a record update expands to, whichever layer it is. -/
def recUpdate (layer : Layer) (names : Array (TSyntax `term)) (values : Array (TSyntax `term))
(record : TSyntax `term) : MacroM (TSyntax `term) :=
  bindArgs (#[record] ++ values) fun ids => do
    let mut body ← `($(layer.op `recordSet) $(ids[0]!) $(names[0]!) $(ids[1]!))
    for i in [1 : names.size] do
      let acc ← freshId "smtRecAcc"
      body ← `($body >>= fun $acc => $(layer.op `recordSet) $acc $(names[i]!) $(ids[i + 1]!))
    return body

/-- A record field's term. -/
def recFieldTerm (field : Syntax) : Syntax :=
  if field.getKind == ``smtRecFieldOf then field[4] else field[2]


/-! ## Reading fields off an identifier

`r.a` reaches the expander as a *single* identifier token, so whether it names something or reads
field `a` off `r` is a question about what is in scope. A macro cannot ask it — `MacroM` can resolve
global names but cannot see the local context — so the identifier leaf expands to a node with the
elaborator below, and everything else in the DSL stays a macro.

Resolution follows Lean's own order: a **local** head wins first, then the longest prefix that
resolves as a name, and what is left over are fields. So `r.a` reads a field off a local `r` even
where a constant `r.a` exists, and `Foo.bar.a` reads one off the constant `Foo.bar`.

An identifier carrying macro scopes is never taken apart: it stands for one binding a macro
introduced, and its components are not a path a user wrote.
-/

/-- The head and the fields read off it, following Lean's resolution order. -/
private def splitProj (id : Ident) : Lean.Elab.TermElabM (Name × List Name) := do
  let name := id.getId
  if name.hasMacroScopes then
    return (name, [])
  let comps := name.components
  -- a local head wins, as in Lean
  if let some head := comps.head? then
    if ((← getLCtx).findFromUserName? head).isSome then
      return (head, comps.drop 1)
  -- otherwise the longest prefix that resolves
  for drop in [0 : comps.length] do
    let keep := comps.length - drop
    let head := (comps.take keep).foldl (· ++ ·) Name.anonymous
    if (← Lean.Elab.Term.resolveId? (mkIdentFrom id head)).isSome then
      return (head, comps.drop keep)
  Lean.throwErrorAt id s!"unknown identifier `{name}`"

/-- Elaborates an identifier of `layer`, reading off whatever fields it names. -/
def elabSmtProj (layer : Layer) (id : Ident) (expected? : Option Lean.Expr)
: Lean.Elab.TermElabM Lean.Expr := do
  let (head, fields) ← splitProj id
  -- with no fields this *is* the identifier as written, and passing it through unchanged is what
  -- keeps its use visible: a rebuilt identifier is not one the unused-variable linter counts
  if fields.isEmpty then
    return ← Lean.Elab.Term.elabTerm (← `(pure $id)) expected?
  -- `identComponents` splits the identifier at its own source ranges, which is what Lean's dot
  -- notation uses and what keeps the head a *reference* the unused-variable linter can see. A
  -- rebuilt identifier spanning the whole path is not one
  let headStx : Ident :=
    match id.raw.identComponents (nFields? := some fields.length) with
    | head :: _ => ⟨head⟩
    | [] => mkIdentFrom id head (canonical := true)
  let mut body ← `(pure $headStx)
  for field in fields do
    -- the binder is hygienic, quotations in `TermElabM` adding macro scopes of their own
    body ← `($body >>= fun arg => $(layer.op `recordGet) arg $(Syntax.mkStrLit field.toString))
  Lean.Elab.Term.elabTerm body expected?

/-- Elaborates a sort-erased identifier, reading off whatever fields it names. -/
@[term_elab smtProjU] def elabSmtProjU : Lean.Elab.Term.TermElab := fun stx expected? => do
  let `(smtProjU% $id) := stx | Lean.Elab.throwUnsupportedSyntax
  elabSmtProj .untyped id expected?




/-! ## Expansion

These are the sort-erased half; the typed one lives beside the typed constructors and is tried
first, declining whatever is not its layer. `Macro.throwUnsupported` is what makes that work: a
declining alternative falls through to the next.
-/

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.untyped do Macro.throwUnsupported
    let stx := t.raw
    match stx.getKind with
    | ``smtIdent =>
      let id : Ident := ⟨stx[0]⟩
      -- `true`/`false` are the base module's, and an identifier naming no field is too
      if id.getId == `true || id.getId == `false then Macro.throwUnsupported
      `(smtProjU% $id)
    | ``smtProj | ``smtPipeProj =>
      let head ← deferSmt layer stx[0]
      let field := Syntax.mkStrLit stx[2].getId.toString
      bindArgs #[head] fun ids => `($(layer.op `recordGet) $(ids[0]!) $field)
    | ``smtRecord =>
      let fields := stx[1].getSepArgs
      let names := fields.map fun field => Syntax.mkStrLit (recFieldName field)
      let terms ← fields.mapM fun field => deferSmt layer (recFieldTerm field)
      -- a field's sort is the one stated, or the one its term turns out to have
      bindArgs terms fun ids => do
        let mut args := #[]
        for i in [0 : fields.size] do
          let srt ← match recFieldSrt? fields[i]! with
            | some srt => `(some ($srt : $(mkIdent `Cvc.Srt)))
            | Option.none => `(Option.none)
          args := args.push (← `(($(names[i]!), $srt, $(ids[i]!))))
        `($(layer.op `mkRecordFrom) #[$args,*])
    | ``smtWith =>
      let fields := stx[3].getSepArgs
      recCheckDistinct fields
      let names := fields.map fun field => Syntax.mkStrLit (recFieldName field)
      let record ← deferSmt layer stx[1]
      let values ← fields.mapIdxM fun i field => do
        let value ← deferSmt layer (recFieldTerm field)
        match recFieldSrt? field with
        | some srt =>
          `($value >>= $(layer.op `checkFieldSrt) $(names[i]!) ($srt : $(mkIdent `Cvc.Srt)))
        | Option.none => pure value
      recUpdate layer names values record
    | _ => Macro.throwUnsupported

end Ext

end
