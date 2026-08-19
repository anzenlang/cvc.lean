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
import all Cvc.Untyped.Solver

public import Cvc.Srt
public import Cvc.Untyped.Core.Value
public import Cvc.Untyped.BVar
public import Cvc.Untyped.Solver
public meta import Cvc.Ext



/-! # Datatypes, sort-erased

A datatype sort is *declared*, in three steps: a constructor declaration collects its selectors, a
datatype declaration collects its constructors, and `Srt.datatype` turns that into a sort. Once the
sort exists, `Srt.getDatatype` reflects it back as a `Datatype` whose constructors and selectors
carry the terms that build and take apart its values.

**A declared sort is fresh, never nominal.** Declaring the same datatype twice gives two *different*
sorts that print identically, and cvc5 rejects any term mixing them:

```
Subexpressions must have the same type: Type 1: Pair, Type 2: Pair
```

So a datatype sort cannot be *rebuilt*, only kept — which is exactly what `Typ` would have to do,
mapping a Lean type to a description `Typ.toSrt` reconstructs on demand. `Typ.datatype` therefore
carries the datatype's **name** and nothing else, and `toSrt` looks the sort up in the scope's
registry, which `Srt.datatype`, `Srt.datatypes` and `Solver.declareDatatype` all write to. A second
declaration under a name already taken is rejected, so the name identifies one sort.

A **record** sort is the other way round, and is the exception worth knowing here: cvc5 builds the
same record sort from the same fields, so it is structural and `Typ.record` rebuilds it rather than
looking it up. Records are still datatypes underneath, which is why `Cvc.Untyped.Theory.Record`
reaches for everything below.

Recursion goes through `addSelectorSelf` for a datatype referring to itself, and
`addSelectorUnresolved` with `Srt.datatypes` for a mutually recursive group.
-/
namespace Cvc public section variable [Ω]

open Untyped (Term Terms BVar BVars)

open cvc5 renaming
  Datatype → Dt, DatatypeDecl → DtD, DatatypeSelector → DtS,
  DatatypeConstructor → DtC, DatatypeConstructorDecl → DtCD



/-! ## Declaring -/

namespace Datatype.Ctor.Decl

@[inherit_doc cvc5.TermManager.mkDatatypeConstructorDecl]
def mk (name : String) : Env Datatype.Ctor.Decl :=
  runUnsafe fun tm => tm.mkDatatypeConstructorDecl name

variable (d : Datatype.Ctor.Decl)

@[inherit_doc DtCD.addSelector]
def addSelector (name : String) (srt : Srt) : Env Datatype.Ctor.Decl :=
  runUnsafe' do d.toUnsafe.addSelector name srt.toUnsafe

/-- Adds a selector whose codomain is the datatype being declared. -/
def addSelectorSelf (name : String) : Env Datatype.Ctor.Decl :=
  runUnsafe' do d.toUnsafe.addSelectorSelf name

/-- Adds a selector whose codomain is another datatype of the same mutually recursive group. -/
def addSelectorUnresolved (name : String) (unresDatatypeName : String)
: Env Datatype.Ctor.Decl :=
  runUnsafe' do d.toUnsafe.addSelectorUnresolved name unresDatatypeName

end Datatype.Ctor.Decl

namespace Datatype.Decl

@[inherit_doc cvc5.TermManager.mkDatatypeDecl]
def mk (name : String) (params : Srts := #[]) (isCoDatatype : Bool := false) : Env Datatype.Decl :=
  runUnsafe fun tm => tm.mkDatatypeDecl name params isCoDatatype

variable (d : Datatype.Decl)

@[inherit_doc DtD.addConstructor]
def addCtor (ctor : Datatype.Ctor.Decl) : Env Datatype.Decl :=
  runUnsafe' do d.toUnsafe.addConstructor ctor.toUnsafe

@[inherit_doc DtD.getNumConstructors]
def countCtors : Nat := d.toUnsafe.getNumConstructors

@[inherit_doc DtD.isParametric]
def isParametric : Bool := d.toUnsafe.isParametric

@[inherit_doc DtD.getName]
def getName : Res String := d.toUnsafe.getName

@[inherit_doc DtD.isResolved]
def isResolved : Env Bool := runUnsafe' d.toUnsafe.isResolved

end Datatype.Decl

namespace Untyped.Solver

/-- Declares a datatype sort from its constructors.

The short path: no parameters and no mutual recursion. `Srt.datatype` is the general one.
-/
def declareDatatype (s : Untyped.Solver) (symbol : String) (ctors : Array Datatype.Ctor.Decl)
: Env Srt := do
  let srt : Srt ←
    runUnsafe' do s.toUnsafe.declareDatatype symbol (ctors.map Datatype.Ctor.Decl.toUnsafe)
  -- registered so that `ToTyp` can name it: see `Srt.ofName`
  registerSort symbol srt.toUnsafe
  return srt

end Untyped.Solver



/-! ## Reflecting

`Srt.getDatatype` is the way in, from a sort that `Srt.isDatatype` holds of.
-/

namespace Datatype.Selector variable (s : Datatype.Selector)

@[inherit_doc DtS.getName]
def getName : Res String := s.toUnsafe.getName

/-- The selector term, the first argument of an `applySelector`. -/
def getTerm : Env Term := runUnsafe' do s.toUnsafe.getTerm

/-- The updater term, the first argument of an `applyUpdater`. -/
def getUpdaterTerm : Env Term := runUnsafe' do s.toUnsafe.getUpdaterTerm

@[inherit_doc DtS.getCodomainSort]
def getCodomainSort : Env Srt := runUnsafe' do s.toUnsafe.getCodomainSort

end Datatype.Selector

namespace Datatype.Ctor variable (c : Datatype.Ctor)

@[inherit_doc DtC.getName]
def getName : Res String := c.toUnsafe.getName

/-- The constructor term, the first argument of an `applyCtor`. -/
def getTerm : Env Term := runUnsafe' do c.toUnsafe.getTerm

/-- The constructor term of a *parametric* datatype, at the given instance of it. -/
def getInstantiatedTerm (retSort : Srt) : Env Term :=
  runUnsafe' do c.toUnsafe.getInstantiatedTerm retSort.toUnsafe

/-- The tester term, the first argument of an `applyTester`. -/
def getTesterTerm : Env Term := runUnsafe' do c.toUnsafe.getTesterTerm

@[inherit_doc DtC.getNumSelectors]
def countSelectors : Nat := c.toUnsafe.getNumSelectors

@[inherit_doc DtC.getSelector]
def getSelector (name : String) : Env Datatype.Selector :=
  runUnsafe' do c.toUnsafe.getSelector name

@[inherit_doc DtC.getSelectorAt]
def getSelectorAt (idx : Fin c.countSelectors) : Datatype.Selector := c.toUnsafe.getSelectorAt idx

instance : GetElem Datatype.Ctor Nat Datatype.Selector fun c idx => idx < c.countSelectors :=
  inferInstanceAs (GetElem DtC Nat DtS fun c idx => idx < c.getNumSelectors)

instance [Monad m] : ForIn m Datatype.Ctor Datatype.Selector :=
  inferInstanceAs (ForIn m DtC DtS)

end Datatype.Ctor

namespace Datatype variable (dt : Datatype)

@[inherit_doc Dt.getName]
def getName : Res String := dt.toUnsafe.getName

@[inherit_doc Dt.getConstructor]
def getCtorNamed (name : String) : Env Datatype.Ctor :=
  runUnsafe' do dt.toUnsafe.getConstructor name

@[inherit_doc Dt.getNumConstructors]
def countCtors : Nat := dt.toUnsafe.getNumConstructors

@[inherit_doc Dt.getConstructorAt]
def getCtorAt (idx : Fin dt.countCtors) : Datatype.Ctor :=
  dt.toUnsafe.getConstructorAt idx

@[inherit_doc getCtorAt]
def getCtorAt? (idx : Nat) : Option Datatype.Ctor :=
  if h : idx < dt.countCtors then dt.getCtorAt ⟨idx, h⟩ else none

@[inherit_doc getCtorAt]
def getCtor (idx : Nat) : Res Datatype.Ctor := do
  let ub := dt.countCtors
  if h : idx < ub then return dt.getCtorAt ⟨idx, h⟩
  else throwUser s!"cannot retrieve constructor {idx}\n{dt} only has {ub} constructor(s)"

instance : GetElem Datatype Nat Datatype.Ctor fun dt idx => idx < dt.countCtors :=
  inferInstanceAs (GetElem Dt Nat DtC fun dt idx => idx < dt.getNumConstructors)

instance [Monad m] : ForIn m Datatype Datatype.Ctor := inferInstanceAs (ForIn m Dt DtC)

/-- Looks a selector up by name, across every constructor. -/
def getSelector (name : String) : Env Datatype.Selector :=
  runUnsafe' do dt.toUnsafe.getSelector name

@[inherit_doc Dt.getParameters]
def getParameters : Env Srts := runUnsafe' do dt.toUnsafe.getParameters

@[inherit_doc Dt.isParametric]
def isParametric : Bool := dt.toUnsafe.isParametric
@[inherit_doc Dt.isCodatatype]
def isCoDatatype : Bool := dt.toUnsafe.isCodatatype
@[inherit_doc Dt.isTuple]
def isTuple : Bool := dt.toUnsafe.isTuple
@[inherit_doc Dt.isRecord]
def isRecord : Bool := dt.toUnsafe.isRecord
@[inherit_doc Dt.isFinite]
def isFinite : Res Bool := dt.toUnsafe.isFinite
@[inherit_doc Dt.isWellFounded]
def isWellFounded : Bool := dt.toUnsafe.isWellFounded

end Datatype



/-! ## Building and taking apart values

Each of these takes the relevant term off a `Ctor` or `Selector` as its first argument,
which is how cvc5 spells datatype application.
-/

namespace Untyped.Term

/-- Applies a constructor to its arguments. -/
def applyCtor (ctor : Term) (args : Terms := #[]) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .APPLY_CONSTRUCTOR (#[ctor] ++ args)

/-- Reads a field out of a datatype value.

Undefined where the value was not built by the selector's own constructor, which is what
`applyTester` is for.
-/
def applySelector (sel : Term) (dt : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .APPLY_SELECTOR #[sel, dt]

/-- Whether a datatype value was built by a given constructor. -/
def applyTester (tester : Term) (dt : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .APPLY_TESTER #[tester, dt]

/-- The datatype value with one field replaced. -/
def applyUpdater (updater : Term) (dt : Term) (newValue : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .APPLY_UPDATER #[updater, dt, newValue]

end Untyped.Term

@[inherit_doc Untyped.Term.applyCtor]
abbrev Datatype.Ctor.apply (ctor : Datatype.Ctor) (args : Terms := #[])
: Env Term := do
  (← ctor.getTerm).applyCtor args

@[inherit_doc Untyped.Term.applySelector]
abbrev Datatype.Selector.apply (sel : Datatype.Selector) (dt : Term) : Env Term := do
  (← sel.getTerm).applySelector dt

@[inherit_doc Untyped.Term.applyUpdater]
abbrev Datatype.Selector.applyUpdate (sel : Datatype.Selector) (dt : Term) (newValue : Term)
: Env Term := do
  (← sel.getUpdaterTerm).applyUpdater dt newValue



/-! ## Matching

A match term picks a body by the constructor its scrutinee was built with. Each case pairs a
*pattern* with the body to use when it applies, and `mkMatch` collects them.

Nothing here needs a quantifier: a case binds its constructor's fields to plain bound variables,
which `Term.mkBVar` already produces. `matchBindCase` builds the variable list cvc5 wants, so that
term never has to be spelled.

Two conditions are cvc5's to check, since both are properties of the datatype's declaration rather
than of any term: the cases must cover every constructor unless one of them is a catch-all, and all
of the bodies must have the same sort.

Cases are tried in order, so a catch-all placed before another case shadows it — the same reading
Lean's own `match` has. cvc5 accepts a catch-all in any position, including as the only case.

The three lookups below exist for the `smt! match … with` notation, whose expansion has a
constructor's *name* and the number of variables written after it and nothing else. They are
ordinary functions, so hand-written matches can use them too.
-/

namespace Untyped.Term

/-- The constructor of the given name, of the datatype this term's sort denotes. -/
def ctorOf (t : Term) (name : String) : Env Datatype.Ctor := do
  let srt ← t.getSort
  if !srt.isDatatype then
    throwUser s!"cannot match on a term of sort `{srt}`, which is not a datatype"
  (← srt.getDatatype).getCtorNamed name

end Untyped.Term

namespace Datatype.Ctor variable (c : Datatype.Ctor)

/-- Fails unless the constructor takes exactly `count` fields.

A match binds one variable per field, so this is what reports a pattern of the wrong width, naming
the constructor rather than leaving an out-of-range index to explain itself.
-/
def checkArity (count : Nat) : Env Unit := do
  if c.countSelectors != count then
    throwUser s!"constructor `{← c.getName}` takes {c.countSelectors} field(s), bound {count}"

/-- A fresh bound variable at the sort of the constructor's field at `idx`. -/
def mkBVarAt (idx : Nat) (name : String) : Env BVar := do
  if h : idx < c.countSelectors then
    Untyped.BVar.mk (← (c.getSelectorAt ⟨idx, h⟩).getCodomainSort) name
  else
    throwUser s!"constructor `{← c.getName}` has no field at index {idx}"

end Datatype.Ctor

namespace Untyped.Term

/-- A match case for a constructor taking no field.

`pattern` is that constructor applied to nothing. A constructor that does take fields needs
`matchBindCase`, which binds them.
-/
def matchCase (pattern body : Term) : Env Term :=
  runUnsafe fun tm => tm.mkTerm .MATCH_CASE #[pattern, body]

/-- A match case binding the variables its pattern mentions.

`pattern` is either a constructor applied to exactly `bvars`, or a single bound variable — which
makes the case a **catch-all**, matching whatever the earlier cases left over. `body` is free to
mention the bound variables.
-/
def matchBindCase (bvars : BVars) (pattern body : Term) : Env Term :=
  runUnsafe fun tm => do
    let vars ← tm.mkTerm .VARIABLE_LIST (bvars.map BVar.toTerm)
    tm.mkTerm .MATCH_BIND_CASE #[vars, pattern, body]

/-- The body of whichever case matches the scrutinee.

Every case must come from `matchCase` or `matchBindCase`, and the resulting term has the sort the
bodies share.
-/
def mkMatch
  (scrutinee : Term) (cases : Terms)
  (_h : 0 < cases.size := by (try grind) <;> fail "failed to prove there is at least one case")
: Env Term :=
  runUnsafe fun tm => tm.mkTerm .MATCH (#[scrutinee] ++ cases)

end Untyped.Term



public meta section

open Lean

/-! ### Matching

`match … with | ctor x y => … | _ => …` over a datatype, binding each constructor's fields
without the writer having to make bound variables.

`match` and `with` are Lean keywords already, so unlike an identifier-shaped atom of a new rule
these reserve nothing. Neither new category needs `behavior := symbol` for the same reason
`smtTerm` does not: every atom here is a symbol rather than an identifier, so nothing would be
reserved either way, and a rule leading with `ident` is what symbol behavior indexes worst.

The alternatives get categories of their own rather than an inline `many` group, since the expander
navigates nodes by index and nesting them would make that unreadable.

The catch-all is spelled `_` and nothing else. A bare identifier is always a constructor name: a
nullary constructor and a variable standing for the scrutinee are the same syntax, and cvc5 reads a
lone variable pattern as the catch-all, so naming the two apart is what keeps `| nil => …` meaning
the constructor. Nothing is lost — the body of a catch-all can mention the scrutinee directly.
-/

/-- One variable bound by a pattern, optionally at a stated sort. -/
declare_syntax_cat smtPatArg
/-- A variable whose sort is inferred. -/
syntax (name := smtPatArg) ident : smtPatArg
/-- A variable at a stated sort, `(x : Lst)`. -/
syntax (name := smtPatArgOf) "(" ident " : " term ")" : smtPatArg

/-- One alternative of a match. -/
declare_syntax_cat smtMatchAlt
/-- An alternative matching one constructor, binding one variable per field. -/
syntax (name := smtAlt) " | " ident (ppSpace smtPatArg)* " => " smtTerm : smtMatchAlt
/-- The catch-all alternative, taken when no earlier one matches. -/
syntax (name := smtAltAny) " | " "_" " => " smtTerm : smtMatchAlt

/-- Matches a datatype term against its constructors. -/
syntax (name := smtMatch)
  withPosition("match " smtTerm " with" (ppLine colGe smtMatchAlt)+)
: smtTerm

/-! The DSL's machinery for these forms lives in `Cvc.Ext`, never in `Cvc`, so that it cannot clash
with the API a user opens.
-/
namespace Ext

/-- The name a pattern variable binds. -/
def patBinderName (arg : Syntax) : Name :=
  if arg.getKind == ``smtPatArgOf then arg[1].getId else arg[0].getId

/-- Whether an identifier is *referenced* anywhere in a piece of syntax.

Used on a match body, before it is expanded, to tell whether a variable the pattern binds is
mentioned at all — which in the typed layer is what decides whether its index can be inferred.

Binders shadow, so this stops at one: a nested alternative or `let` that rebinds the name is
talking about a different variable, and descending into its body would report an occurrence that
is not one.
-/
partial def occursIn (name : Name) : Syntax → Bool
  | .ident _ _ id _ => id == name
  | .node _ kind args =>
    if kind == ``smtAlt && args[2]!.getArgs.any (patBinderName · == name) then
      -- shadowed in the body; only a sort ascription of this alternative could still name it, and
      -- the binders themselves must not count, being the very thing doing the shadowing
      args[2]!.getArgs.any fun arg => arg.getKind == ``smtPatArgOf && occursIn name arg[3]
    else if kind == ``smtLet && args[1]!.getId == name then
      -- shadowed in the body, but the bound value is evaluated before the shadowing
      occursIn name args[3]!
    else args.any (occursIn name)
  | _ => false

/-- Parses a pattern's variables into their binders and their sort ascriptions, where given. -/
def patArgs (args : Array Syntax) : MacroM (Array (Ident × Option (TSyntax `term))) :=
  args.mapM fun arg => do
    match arg.getKind with
    | ``smtPatArg => return (⟨arg[0]⟩, none)
    | ``smtPatArgOf => return (⟨arg[1]⟩, some ⟨arg[3]⟩)
    | k => Macro.throwErrorAt arg s!"unsupported pattern variable (kind `{k}`)"


/-- Expands one alternative of a `match` into a term building that case.

The variables a pattern binds are spliced as binders *as the writer wrote them*, never through
`mkIdent`, or hygiene would hide them from the body. Everything the expansion binds for its own
sake is macro-scoped instead, so the two cannot collide.

Each variable is bound twice: once to the bound variable itself, which the case needs, and once —
under the writer's name — to the term it converts to, which is what the body may mention. That
saves the coercion having to fire at every use.

This is the sort-erased arm: a bound variable is made at the field's declared sort and the pattern
is applied by hand. The typed one, beside the typed constructors, lets `Datatype.Ctor.case` build
the pattern and check both the arity and the sorts.
-/
def expandMatchAltU (layer : Layer) (scrutId : Ident) (alt : Syntax)
: MacroM (TSyntax `term) := do
  match alt.getKind with
  | ``smtAltAny =>
    let body ← deferSmt layer alt[3]
    let bvId ← freshId "smtAnyVar"
    let bodyId ← freshId "smtBody"
    let srtId ← freshId "smtSrt"
    `($(layer.op `getSort) $scrutId >>= fun $srtId =>
      $(layer.name `BVar.mk) $srtId "_" >>= fun $bvId =>
      $body >>= fun $bodyId =>
      $(layer.op `matchBindCase) #[$bvId] ($bvId).toTerm $bodyId)
  | ``smtAlt =>
    let ctor : Ident := ⟨alt[1]⟩
    let rawBody := alt[4]
    let body ← deferSmt layer rawBody

    let pats ← patArgs alt[2].getArgs
    let binders := pats.map Prod.fst
    let mut vars : Array Ident := #[]
    for idx in [0 : pats.size] do
      vars := vars.push (← freshId s!"smtBVar{idx}")
    let bvIds := vars
    let bvTerms ← bvIds.mapM fun id => `(($id).toTerm)

    let ctorId ← freshId "smtCtor"
    let bodyId ← freshId "smtBody"

    for (_, typ?) in pats do
      if let some typ := typ? then
        Macro.throwErrorAt typ
          "a sort ascription has no meaning in the sort-erased layer, where a field's sort comes \
          from the datatype's declaration"
    let ctorTermId ← freshId "smtCtorTerm"
    let patId ← freshId "smtPat"
    -- built innermost outwards, so each binder is in scope of everything after it
    let mut acc ←
      if pats.isEmpty
      then `($(layer.op `matchCase) $patId $bodyId)
      else `($(layer.op `matchBindCase) #[ $bvIds,* ] $patId $bodyId)
    -- the body, under the writer's names for the variables the pattern binds
    acc ←
      if pats.isEmpty
      then `($body >>= fun $bodyId => $acc)
      else `((fun $binders* => $body) $bvTerms* >>= fun $bodyId => $acc)
    acc ← `($(layer.op `applyCtor) $ctorTermId #[ $bvTerms,* ] >>= fun $patId => $acc)
    acc ← `(($ctorId).getTerm >>= fun $ctorTermId => $acc)
    for idx in [0 : pats.size] do
      let jdx := pats.size - 1 - idx
      let name : TSyntax `term := quote pats[jdx]!.fst.getId.toString
      let at' : TSyntax `term := quote jdx
      acc ← `(($ctorId).mkBVarAt $at' $name >>= fun $(bvIds[jdx]!) => $acc)
    acc ← `(($ctorId).checkArity $(quote pats.size) >>= fun _ => $acc)
    `($(layer.op `ctorOf) $scrutId $(quote ctor.getId.toString) >>= fun $ctorId => $acc)
  | k => Macro.throwErrorAt alt s!"unsupported match alternative (kind `{k}`)"

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.untyped do Macro.throwUnsupported
    let stx := t.raw
    unless stx.getKind == ``smtMatch do Macro.throwUnsupported
    let scrut ← deferSmt layer stx[1]
    let scrutId ← freshId "smtScrut"
    let alts ← stx[3].getArgs.mapM (expandMatchAltU layer scrutId)
    let body ← bindArgs alts fun ids => `($(layer.op `mkMatch) $scrutId #[ $ids,* ])
    `($scrut >>= fun $scrutId => $body)

end Ext

end
