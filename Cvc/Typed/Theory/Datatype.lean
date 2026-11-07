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
import all Cvc.Typed.Core.Defs
import all Cvc.Untyped.Theory.Datatype

public import Cvc.Untyped.Theory.Datatype
public meta import Cvc.Ext
public import Cvc.Typed.Core.Solver
public import Cvc.Gen.TypedView
public import Cvc.Typed.Core.View



/-! # Datatypes, typed

A declared datatype is used at a Lean index. Give a Lean type a `ToTyp` instance naming the
datatype, declare the datatype in the scope (`Srt.datatype`, `Solver.declareDatatype`), and
`Term Lst` is a term like any other:

```lean
structure Lst where private mk ::
instance : ToTyp Lst := ⟨.datatype "Lst"⟩

-- in `Env`, once `Lst := nil | cons (head : Int) (tail : Lst)` is declared
let cons ← Datatype.ctor Lst "cons"      -- `Ctor Lst`
let nil ← Datatype.ctor Lst "nil"
let head ← cons.field Int "head"         -- `Field Lst Int`
let l ← cons.apply2 (← Term.mkInt 1) (← nil.apply)
let h ← head.get l                       -- `Term Int`
```

Which constructors a datatype has, and the sorts of their fields, are facts about its declaration:
`Datatype.ctor` and `Ctor.field` look a name up and check the sorts once, and the `Ctor α` or
`Field α β` they answer carries the index from there on.
-/
-- cvc5 makes a fresh sort at every declaration, so the scope keeps each declared sort under its
-- name; `Typ.datatype` carries the name, and `Srt.of α` looks the sort up.
namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Term → T



namespace Datatype

/-- The constructor arguments of one application, each carrying its own index. -/
abbrev Args := List ((β : Type) × ToTyp β × Term β)
-- Shaped like `BVars`, down to the `ToTyp` field: without it the sigma's layout is not known across
-- a module boundary and the erasure below does not compile.

namespace Args

/-- No arguments. -/
abbrev nil : Args := []

/-- Adds an argument in front of the ones collected so far: `.cons a (.cons b .nil)` is `a`, `b`. -/
abbrev cons [ToTyp β] (arg : Term β) (rest : Args) : Args := ⟨β, inferInstance, arg⟩ :: rest

/-- The sort-erased terms, in field order. -/
def toUntyped (args : Args) : Untyped.Terms :=
  -- `foldl`, not `foldr`: `cons` reads in field order here, unlike `BVars.push` which prepends
  args.foldl (init := Array.mkEmpty args.length) fun acc ⟨_, _, arg⟩ => acc.push arg.erase

@[inherit_doc toUntyped]
abbrev erase := @toUntyped

end Args



/-- A datatype constructor, at the index of the datatype it builds. -/
structure Ctor (α : Type) where
  private mk ::
  private ctor : Cvc.Datatype.Ctor
  private term : Untyped.Term
  private tester : Untyped.Term

/-- One field of a datatype constructor, at the datatype's index and the field's.

The typed counterpart of the selector `Cvc.Datatype.Selector`, which reflects a field sort-erased.
-/
structure Field (α β : Type) where
  private mk ::
  private sel : Cvc.Datatype.Selector
  private term : Untyped.Term
  private updater : Untyped.Term
-- Named `Field` rather than `Selector` so it does not collide with `Datatype.Selector`, the
-- sort-erased reflection type it is built from.

/-- The datatype the index names, reflected.

Fails if nothing has been declared under that name in this scope.
-/
def reflect (α : Type) [ToTyp α] : Env Cvc.Datatype := do
  let srt ← Srt.of α
  if !srt.isDatatype then
    throwUser s!"sort `{srt}` is not a datatype"
  srt.getDatatype

/-- The constructor of the given name. -/
def ctor (α : Type) [ToTyp α] (name : String) : Env (Ctor α) := do
  let c ← (← reflect α).getCtorNamed name
  return ⟨c, ← c.getTerm, ← c.getTesterTerm⟩

/-- The sort-erased constructor it reflects, for free. -/
def Ctor.toUntyped (c : Ctor α) : Cvc.Datatype.Ctor := c.ctor

@[inherit_doc Ctor.toUntyped]
abbrev Ctor.erase (c : Ctor α) : Cvc.Datatype.Ctor := c.toUntyped

/-- Types a reflected constructor at the datatype `α`, checking that `α` is what it builds.

The reflection counterpart of `Datatype.ctor`, which looks a constructor up by name. A constructor
of a parametric datatype read off the uninstantiated declaration builds the parametric sort, not an
instance of it, and is refused. `toTyped` infers `α` from the expected type; `typeCheckAs` and
`typeCheck` are the same two functions under the names that say what they do.
-/
def _root_.Cvc.Datatype.Ctor.toTypedAs (α : Type) [ToTyp α] (c : Cvc.Datatype.Ctor)
: Env (Ctor α) := do
  let term ← c.getTerm
  let built ← (← term.getSort).getDatatypeConstructorCodomainSort
  let want ← Srt.of α
  if built != want then
    throwUser s!"cannot type constructor `{← c.getName}` at `{want}`, it builds `{built}`"
  return ⟨c, term, ← c.getTesterTerm⟩

@[inherit_doc Cvc.Datatype.Ctor.toTypedAs]
def _root_.Cvc.Datatype.Ctor.toTyped [ToTyp α] (c : Cvc.Datatype.Ctor) : Env (Ctor α) :=
  c.toTypedAs α

@[inherit_doc Cvc.Datatype.Ctor.toTypedAs]
abbrev _root_.Cvc.Datatype.Ctor.typeCheckAs := @Cvc.Datatype.Ctor.toTypedAs

@[inherit_doc Cvc.Datatype.Ctor.toTypedAs]
abbrev _root_.Cvc.Datatype.Ctor.typeCheck := @Cvc.Datatype.Ctor.toTyped

end Datatype

open Typed.Datatype (Args Ctor Field)



namespace Datatype.Ctor variable (c : Ctor α)

/-- The constructor's name. -/
def getName : Res String := c.ctor.getName

/-- How many fields the constructor takes. -/
def countFields : Nat := c.ctor.countSelectors

/-- The sorts of the constructor's fields, in order. -/
def fieldSorts : Env Srts := do
  let mut srts := Array.mkEmpty c.countFields
  -- a constructor iterates over its selectors, which saves an index and its proof
  for sel in c.ctor do
    srts := srts.push (← sel.getCodomainSort)
  return srts

/-- Applies the constructor, failing unless its arguments' number and sorts are its fields'. -/
def apply (args : Args := .nil) : Env (Term α) := do
  let expected ← c.fieldSorts
  let terms := args.erase
  if terms.size != expected.size then
    throwUser s!"constructor `{← c.getName}` takes {expected.size} argument(s), got {terms.size}"
  for h : idx in [0 : terms.size] do
    let actual ← terms[idx].getSort
    let some want := expected[idx]? | throwInternal "field sorts and arguments disagree in size"
    if actual != want then
      throwUser
        s!"argument {idx} of constructor `{← c.getName}` should have sort `{want}`, got `{actual}`"
  T.applyCtor c.term terms

@[inherit_doc apply]
def apply1 [ToTyp β₁] (fst : Term β₁) : Env (Term α) := c.apply (.cons fst .nil)

@[inherit_doc apply]
def apply2 [ToTyp β₁] [ToTyp β₂] (fst : Term β₁) (snd : Term β₂) : Env (Term α) :=
  c.apply (.cons fst (.cons snd .nil))

@[inherit_doc apply]
def apply3 [ToTyp β₁] [ToTyp β₂] [ToTyp β₃] (fst : Term β₁) (snd : Term β₂) (thd : Term β₃) : Env (Term α) :=
  c.apply (.cons fst (.cons snd (.cons thd .nil)))

/-- Whether a value was built by this constructor. -/
def is (t : Term α) : Env (Term Bool) := T.applyTester c.tester t.erase

/-- The field of the given name, at the Lean type `β` of its sort, failing if the sorts differ. -/
def field (β : Type) [ToTyp β] (name : String) : Env (Field α β) := do
  let sel ← c.ctor.getSelector name
  let actual ← sel.getCodomainSort
  let want ← Srt.of β
  if actual != want then
    throwUser
      s!"selector `{name}` of constructor `{← c.getName}` has sort `{actual}`, not `{want}`"
  return ⟨sel, ← sel.getTerm, ← sel.getUpdaterTerm⟩

end Datatype.Ctor



namespace Datatype

/-! ## Matching

A match picks a body by the constructor its scrutinee was built with: `Term.mkMatch` takes the
scrutinee and an array of `Case α β`, whose bodies all have the index `β`. `Ctor.case` binds the
constructor's fields to bound variables, pushed in field order as for `Solver.defineFun`, and checks
their sorts. Every constructor needs a case, unless a `Datatype.caseAny` catches the rest; cvc5
checks that.
-/

/-- One case of a match on a `Term α`, producing a `Term β`. -/
structure Case (α β : Type) where
  private mk ::
  private term : Untyped.Term

/-- The sort-erased case term it wraps, for free, as the sort-erased `Term.mkMatch` takes one.

There is no way back: a sort-erased case is an ordinary `Term`, with no type of its own to hang a
conversion on.
-/
def Case.toUntyped (c : Case α β) : Untyped.Term := c.term

@[inherit_doc Case.toUntyped]
abbrev Case.erase (c : Case α β) : Untyped.Term := c.toUntyped

end Datatype

open Typed.Datatype (Case)



namespace Datatype.Ctor variable (c : Ctor α)

/-- Fails unless the constructor takes exactly `count` fields. -/
def checkArity (count : Nat) : Env Unit := c.ctor.checkArity count

/-- A fresh sort-erased bound variable at the sort of the constructor's field at `idx`.

`Untyped.BVar.typeCheck` puts an index on it.
-/
def mkBVarAt (idx : Nat) (name : String) : Env Untyped.BVar := c.ctor.mkBVarAt idx name

/-- `case`, with the fields bound to sort-erased variables (from `mkBVarAt`). -/
def caseErased (vars : Untyped.BVars) (body : Term β) : Env (Case α β) := do
  let expected ← c.fieldSorts
  if vars.size != expected.size then
    throwUser s!"constructor `{← c.getName}` takes {expected.size} field(s), bound {vars.size}"
  for h : idx in [0 : vars.size] do
    let actual ← vars[idx].toTerm.getSort
    let some want := expected[idx]? | throwInternal "field sorts and bound variables disagree"
    if actual != want then
      throwUser
        s!"variable {idx} bound by constructor `{← c.getName}` should have sort `{want}`, \
          got `{actual}`"
  let pattern ← T.applyCtor c.term (vars.map Untyped.BVar.toTerm)
  -- a constructor with no field binds nothing, and cvc5 wants the unbound form there
  let term ←
    if vars.isEmpty
    then T.matchCase pattern body.erase
    else T.matchBindCase vars pattern body.erase
  return ⟨term⟩
-- Beside `case` because a match need not give every field an index: a field the body ignores has
-- no index to infer one from, so `smt! match … with` binds every field sort-erased and re-types
-- only those the body mentions.

/-- The case taken when the scrutinee was built by this constructor.

`args` binds the constructor's fields, in field order, and `body` may mention them. Fails unless
their number and sorts are the fields'.
-/
def case (args : BVars := []) (body : Term β) : Env (Case α β) := c.caseErased args.erase body

/-- The case taken when the scrutinee was built by this constructor, which takes no field. -/
def case0 (body : Term β) : Env (Case α β) := c.case [] body

@[inherit_doc case]
def case1 [ToTyp β₁] (fst : BVar β₁) (body : Term β) : Env (Case α β) :=
  c.case (BVars.push fst []) body

@[inherit_doc case]
def case2 [ToTyp β₁] [ToTyp β₂]
  (fst : BVar β₁) (snd : BVar β₂) (body : Term β)
: Env (Case α β) :=
  c.case (BVars.push snd (BVars.push fst [])) body

@[inherit_doc case]
def case3 [ToTyp β₁] [ToTyp β₂] [ToTyp β₃]
  (fst : BVar β₁) (snd : BVar β₂) (thd : BVar β₃) (body : Term β)
: Env (Case α β) :=
  c.case (BVars.push thd (BVars.push snd (BVars.push fst []))) body

end Datatype.Ctor



namespace Datatype

/-- The case taken when no earlier one was.

`v` stands for the scrutinee itself, so `body` may mention it. A match needs one of these unless its
cases already cover every constructor.
-/
def caseAny [ToTyp α] (v : BVar α) (body : Term β) : Env (Case α β) := do
  let vars := (BVars.push v []).erase
  return ⟨← T.matchBindCase vars v.toTerm.erase body.erase⟩

end Datatype



namespace Term

/-- `Datatype.ctor` at the datatype of a term's index: the constructor of the given name. -/
def ctorOf [ToTyp α] (_scrutinee : Term α) (name : String) : Env (Ctor α) :=
  Datatype.ctor α name
-- What `smt! match … with` expands to, where the scrutinee is at hand and its index has no name to
-- spell.

/-- The body of whichever case matches the scrutinee.

Fails unless every constructor of `α` has a case, or one of them is a `Datatype.caseAny`.
-/
def mkMatch
  (scrutinee : Term α) (cases : Array (Case α β))
  (_h : 0 < cases.size := by (try grind) <;> fail "failed to prove there is at least one case")
: Env (Term β) :=
  T.mkMatch scrutinee.erase (cases.map Datatype.Case.term) (by simpa using _h)

end Term



namespace Datatype.Field variable (sel : Field α β)

/-- The sort-erased selector it was built from, for free. -/
def toUntyped : Cvc.Datatype.Selector := sel.sel

@[inherit_doc toUntyped]
abbrev erase : Cvc.Datatype.Selector := sel.toUntyped

/-- Reads the field out of a value.

Undefined where the value was not built by the selector's own constructor, which is what
`Ctor.is` is for.
-/
def get (t : Term α) : Env (Term β) := T.applySelector sel.term t.erase

/-- The value with this field replaced. -/
def update (t : Term α) (v : Term β) : Env (Term α) :=
  T.applyUpdater sel.updater t.erase v.erase

end Datatype.Field

/-- Types a reflected selector at the datatype `α` and the field `β`, checking both sorts.

The reflection counterpart of `Datatype.Ctor.field`, which looks a selector up by name. `toTyped`
infers `α` and `β` from the expected type; `typeCheckAs` and `typeCheck` are the same two functions
under the names that say what they do.
-/
def _root_.Cvc.Datatype.Selector.toTypedAs (α β : Type) [ToTyp α] [ToTyp β]
  (sel : Cvc.Datatype.Selector)
: Env (Field α β) := do
  let term ← sel.getTerm
  let srt ← term.getSort
  let dom ← srt.getDatatypeSelectorDomainSort
  let cod ← srt.getDatatypeSelectorCodomainSort
  let dom' ← Srt.of α
  let cod' ← Srt.of β
  if dom != dom' then
    throwUser s!"cannot type selector `{← sel.getName}` on `{dom'}`, it selects from `{dom}`"
  if cod != cod' then
    throwUser s!"cannot type selector `{← sel.getName}` at `{cod'}`, it selects `{cod}`"
  return ⟨sel, term, ← sel.getUpdaterTerm⟩

@[inherit_doc Cvc.Datatype.Selector.toTypedAs]
def _root_.Cvc.Datatype.Selector.toTyped [ToTyp α] [ToTyp β] (sel : Cvc.Datatype.Selector)
: Env (Field α β) := sel.toTypedAs α β

@[inherit_doc Cvc.Datatype.Selector.toTypedAs]
abbrev _root_.Cvc.Datatype.Selector.typeCheckAs := @Cvc.Datatype.Selector.toTypedAs

@[inherit_doc Cvc.Datatype.Selector.toTypedAs]
abbrev _root_.Cvc.Datatype.Selector.typeCheck := @Cvc.Datatype.Selector.toTyped



/-! ## Viewing a datatype operation

Generic over every datatype: constructors and fields come back by name, and the kids' sorts as a
list of `Typ`s that matching refines. Records, tuples and nullables are datatypes to cvc5, so this
covers them too; `Term.recordFields?`, `Term.pairComponents?` and `Term.nullableCases?` take them
apart at a known index instead.
-/

/-- A constructor's arguments, each a `Term σ.Denote` at its sort `σ`, in order.

Empty for a constant constructor such as `nil`.
-/
inductive View.Datatype.Fields : List Typ → Type where
  /-- No argument. -/
  | nil : View.Datatype.Fields []
  /-- One more argument, in front of the others. -/
  | cons (t : Term τ.Denote) (rest : View.Datatype.Fields τs) : View.Datatype.Fields (τ :: τs)

/-- The arguments as cvc5 prints them. -/
def View.Datatype.Fields.toStrings : View.Datatype.Fields doms → List String
  | .nil => []
  | .cons t rest => toString t :: rest.toStrings

/-- A datatype operation of sort `τ`, taken apart one level. -/
protected inductive View.Datatype : Typ → Type where
  /-- A constructor applied to its arguments, none for a constant constructor. -/
  | construct {τ : Typ} (ctor : String) (doms : List Typ) (args : View.Datatype.Fields doms)
    : View.Datatype τ
  /-- A field read off `arg`, a term of the datatype sort `σ`. -/
  | selectField {τ : Typ} (field : String) (σ : Typ) (arg : Term σ.Denote) : View.Datatype τ
  /-- `arg` with its field replaced by `value`, a term of sort `σ`. -/
  | updateField {τ : Typ} (field : String) (σ : Typ) (arg : Term τ.Denote) (value : Term σ.Denote)
    : View.Datatype τ
  /-- Whether `arg`, of the datatype sort `σ`, was built by the constructor `ctor`. -/
  | testCtor (ctor : String) (σ : Typ) (arg : Term σ.Denote) : View.Datatype .bool

/-- Takes a datatype operation of sort `τ` apart one level, `none` for any other term.

Also `none` when a kid's sort is one no `Typ` describes.
-/
def View.Datatype.of (τ : Typ) (t : Term τ.Denote) : Env (Option (View.Datatype τ)) :=
  match τ, Untyped.View.Datatype.of? t.erase with
  | _, some (.construct ctor args) => do
    let some ⟨doms, args⟩ ← go args.toList | return none
    return some (.construct ctor doms args)
  | _, some (.selectField field arg) => do
    let some σ ← View.typOf? arg | return none
    return some (.selectField field σ (View.reindex arg))
  | _, some (.updateField field arg value) => do
    let some σ ← View.typOf? value | return none
    return some (.updateField field σ (View.reindex arg) (View.reindex value))
  | .bool, some (.testCtor ctor arg) => do
    let some σ ← View.typOf? arg | return none
    return some (.testCtor ctor σ (View.reindex arg))
  | _, _ => return none
where
  /-- A constructor's arguments, with their sorts. -/
  go : List Untyped.Term → Env (Option ((doms : List Typ) × View.Datatype.Fields doms))
    | [] => return some ⟨[], .nil⟩
    | k :: ks => do
      let some σ ← View.typOf? k | return none
      let some ⟨σs, rest⟩ ← go ks | return none
      return some ⟨σ :: σs, .cons (View.reindex k) rest⟩

register_typed_view% Cvc.Typed.View.Datatype
  [construct APPLY_CONSTRUCTOR, selectField APPLY_SELECTOR, updateField APPLY_UPDATER,
    testCtor APPLY_TESTER]



public meta section

open Lean

/-! ## `smt! match`

```lean
smt! match l with
  | cons h t => h * 2
  | nil => 0
```

A bare identifier in a pattern is a constructor; `_` alone is the catch-all. A field's index is
inferred from its uses in the body; a nested match's scrutinee needs an ascription,
`| cons h (t : Lst) => match t with …`.
-/
-- The syntax is declared once, beside the sort-erased constructors; this layer adds only its own
-- expansion, tried first and declining whatever is not its layer. Sort-erased, a bound variable is
-- made at the field's declared sort and the pattern applied by hand, where `Datatype.Ctor.case`
-- builds the pattern here and checks the arity and the sorts. Every field is bound sort-erased
-- first, and only those the body can name are re-typed: a field the body ignores offers no index
-- to infer. The DSL's machinery lives in `Cvc.Ext`, never in `Cvc`, so that it cannot clash with
-- the API a user opens.
namespace Ext

open Cvc.Ext

/-- Expands one alternative of a typed `match` into a term building that case. -/
def expandMatchAltT (layer : Layer) (scrutId : Ident) (alt : Syntax)
: MacroM (TSyntax `term) := do
  match alt.getKind with
  | ``smtAltAny =>
    let body ← deferSmt layer alt[3]
    let bvId ← freshId "smtAnyVar"
    let bodyId ← freshId "smtBody"
    -- the index comes from `caseAny`, which shares it with the scrutinee
    `($(layer.name `BVar.mk) "_" >>= fun $bvId =>
      $body >>= fun $bodyId =>
      $(layer.name `Datatype.caseAny) $bvId $bodyId)
  | ``smtAlt =>
    let ctor : Ident := ⟨alt[1]⟩
    let rawBody := alt[4]
    let body ← deferSmt layer rawBody

    let pats ← patArgs alt[2].getArgs
    let mut vars : Array Ident := #[]
    for idx in [0 : pats.size] do
      vars := vars.push (← freshId s!"smtBVar{idx}")
    let bvIds := vars

    let ctorId ← freshId "smtCtor"
    let bodyId ← freshId "smtBody"

    -- built innermost outwards, so each binder is in scope of everything after it
    let mut acc ← `(($ctorId).caseErased #[ $bvIds,* ] $bodyId)
    acc ← `($body >>= fun $bodyId => $acc)
    for idx in [0 : pats.size] do
      let jdx := pats.size - 1 - idx
      let (binder, typ?) := pats[jdx]!
      let used := occursIn binder.getId rawBody
      unless typ?.isNone && !used do
        let tc ←
          match typ? with
          | some typ => `((($(bvIds[jdx]!)).toTerm).typeCheckAs $typ)
          | none => `((($(bvIds[jdx]!)).toTerm).typeCheck)
        -- a used variable is bound under the writer's own name, so a mismatch in the body names
        -- it; one that is only ascribed is bound out of sight, its check being the whole point
        let bindTo ← if used then pure binder else freshId "smtChecked"
        acc ← `($tc >>= fun $bindTo => $acc)
    for idx in [0 : pats.size] do
      let jdx := pats.size - 1 - idx
      let name : TSyntax `term := quote pats[jdx]!.fst.getId.toString
      acc ← `(($ctorId).mkBVarAt $(quote jdx) $name >>= fun $(bvIds[jdx]!) => $acc)
    acc ← `(($ctorId).checkArity $(quote pats.size) >>= fun _ => $acc)
    `($(layer.op `ctorOf) $scrutId $(quote ctor.getId.toString) >>= fun $ctorId => $acc)
  | k => Macro.throwErrorAt alt s!"unsupported match alternative (kind `{k}`)"

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.typed do Macro.throwUnsupported
    let stx := t.raw
    unless stx.getKind == ``smtMatch do Macro.throwUnsupported
    let scrut ← deferSmt layer stx[1]
    let scrutId ← freshId "smtScrut"
    let alts ← stx[3].getArgs.mapM (expandMatchAltT layer scrutId)
    let body ← bindArgs alts fun ids => `($(layer.op `mkMatch) $scrutId #[ $ids,* ])
    `($scrut >>= fun $scrutId => $body)

end Ext

end
