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
public import Cvc.Typed.Solver



/-! # Datatypes, typed

A datatype's sort is *declared*, and cvc5 makes a fresh one every time, so the scope keeps each
declared sort in its registry under a name and `Typ.datatype` carries that name. A Lean index
therefore names a datatype the same way it names any other sort, and `Srt.of α` finds it — which is
what lets everything below take an index rather than a handle.

Two things are still runtime facts about a declaration rather than static ones: which constructors a
datatype has, and what sort each of their fields is. So `Datatype.ctor` and `Ctor.selector` look
their names up and **check** the sorts, then hand back a `Ctor α` or a `Selector α β` that carries
the index from there on. It is the `Untyped.Term.typeCheck` trick, applied once at the point where
a name becomes a Lean type.
-/
namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Term → T



namespace Datatype

/-- The constructor arguments of one application, each carrying its own index.

Shaped like `BVars`, down to the `ToTyp` field: without it the sigma's layout is not known across a
module boundary and the erasure below does not compile.
-/
abbrev Args := List ((β : Type) × ToTyp β × Term β)

namespace Args

/-- No arguments. -/
abbrev nil : Args := []

/-- Adds an argument in front of the ones collected so far, so a spine reads in field order. -/
abbrev cons [ToTyp β] (arg : Term β) (rest : Args) : Args := ⟨β, inferInstance, arg⟩ :: rest

/-- Erases the indices, keeping field order. -/
def erase (args : Args) : Untyped.Terms :=
  -- `foldl`, not `foldr`: `cons` reads in field order here, unlike `BVars.push` which prepends
  args.foldl (init := Array.mkEmpty args.length) fun acc ⟨_, _, arg⟩ => acc.push arg.erase

end Args



/-- A datatype constructor, at the index of the datatype it builds. -/
structure Ctor (α : Type) where
  private mk ::
  private ctor : Cvc.Datatype.Ctor
  private term : Untyped.Term
  private tester : Untyped.Term

/-- One field of a datatype constructor, at the datatype's index and the field's.

Named `Field` rather than `Selector` so it does not collide with `Datatype.Selector`, the
sort-erased reflection type it is built from.
-/
structure Field (α β : Type) where
  private mk ::
  private term : Untyped.Term
  private updater : Untyped.Term

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

end Datatype

open Datatype (Args Ctor Field)



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

/-- Applies the constructor to its arguments.

The arity and the arguments' sorts are checked here rather than left to cvc5, since a datatype's
field sorts are a property of its declaration and not of any index.
-/
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

/-- The selector of the given name, at the field index `β`.

`β` is given rather than inferred, because a field's sort is a runtime property of the declaration.
It is checked against the selector's own codomain, so a `Field α β` that exists is one whose index
is right.
-/
def field (β : Type) [ToTyp β] (name : String) : Env (Field α β) := do
  let sel ← c.ctor.getSelector name
  let actual ← sel.getCodomainSort
  let want ← Srt.of β
  if actual != want then
    throwUser
      s!"selector `{name}` of constructor `{← c.getName}` has sort `{actual}`, not `{want}`"
  return ⟨← sel.getTerm, ← sel.getUpdaterTerm⟩

end Datatype.Ctor



namespace Datatype

/-! ## Matching

A match picks a body by the constructor its scrutinee was built with. `Case α β` is one case of a
match on a `Term α` whose bodies are `Term β`, so the index states what a sort-erased match can
only check at runtime: that every body agrees.

A case binds its constructor's fields to ordinary bound variables, collected right to left by
`BVars.push` exactly as `Solver.defineFun` collects its parameters. Their sorts are checked against
the constructor's fields here, for the same reason `Ctor.apply` checks its arguments: what fields a
constructor has is a property of the declaration and not of any index.

Exhaustiveness stays cvc5's to check, being a property of the declaration too. `Datatype.caseAny`
builds the catch-all that discharges it.
-/

/-- One case of a match on a `Term α`, producing a `Term β`. -/
structure Case (α β : Type) where
  private mk ::
  private term : Untyped.Term

end Datatype

open Datatype (Case)



namespace Datatype.Ctor variable (c : Ctor α)

/-- Fails unless the constructor takes exactly `count` fields. -/
def checkArity (count : Nat) : Env Unit := c.ctor.checkArity count

/-- A fresh bound variable at the sort of the constructor's field at `idx`.

Sort-erased, because the sort is a property of the declaration and no index is needed to ask for
it. `Untyped.Term.typeCheck` is what puts an index back on, for the fields a body actually uses.
-/
def mkBVarAt (idx : Nat) (name : String) : Env Untyped.BVar := c.ctor.mkBVarAt idx name

/-- The case taken when the scrutinee was built by this constructor, its variables sort-erased.

`case` is the form to reach for; this one exists because a match need not give every field an
index. A field the body ignores has no index to infer one from, so the `smt! match … with`
notation binds all of them sort-erased and re-types only those the body mentions.
-/
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

/-- The case taken when the scrutinee was built by this constructor.

`args` binds the constructor's fields, and `body` is free to mention them. Their sorts are checked
against the constructor's, so a `Case` that exists is one whose pattern is well formed.
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

/-- The constructor of the given name, of the datatype the term's index names.

The same lookup as `Datatype.ctor`, reached from a term rather than from the index it carries. That
is what the `smt! match … with` notation expands to, where the scrutinee is at hand and the index
has no name to spell.
-/
def ctorOf [ToTyp α] (_scrutinee : Term α) (name : String) : Env (Ctor α) :=
  Datatype.ctor α name

/-- The body of whichever case matches the scrutinee.

Every constructor of `α` must have a case, unless one of them is a `Datatype.caseAny`. That is
cvc5's to check, and it fails here if it does not hold.
-/
def mkMatch
  (scrutinee : Term α) (cases : Array (Case α β))
  (_h : 0 < cases.size := by (try grind) <;> fail "failed to prove there is at least one case")
: Env (Term β) :=
  T.mkMatch scrutinee.erase (cases.map Datatype.Case.term) (by simpa using _h)

end Term



namespace Datatype.Field variable (sel : Field α β)

/-- Reads the field out of a value.

Undefined where the value was not built by the selector's own constructor, which is what
`Ctor.is` is for.
-/
def get (t : Term α) : Env (Term β) := T.applySelector sel.term t.erase

/-- The value with this field replaced. -/
def update (t : Term α) (v : Term β) : Env (Term α) :=
  T.applyUpdater sel.updater t.erase v.erase

end Datatype.Field
