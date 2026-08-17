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
import all Cvc.Untyped.Term.Defs
import all Cvc.Untyped.Solver

public import Cvc.Srt
public import Cvc.Untyped.BVar
public import Cvc.Untyped.Term.Value
public import Cvc.Untyped.Solver



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

So a datatype sort has to be created once and kept, exactly like the `Srt` a `Solver.declareSrt`
answers — it cannot be recovered from a name later. This is also why `ToTyp` has no datatype case:
that class maps a Lean type to a `Typ` which `toSrt` *rebuilds* on demand, and rebuilding is
precisely what a datatype sort does not survive.

Recursion goes through `addSelectorSelf` for a datatype referring to itself, and
`addSelectorUnresolved` with `Srt.datatypes` for a mutually recursive group.
-/
namespace Cvc public section variable [Ω]

open Untyped (Term Terms BVar BVars)

open cvc5 renaming
  Datatype → Dt, DatatypeDecl → DtD, DatatypeSelector → DtS,
  DatatypeConstructor → DtC, DatatypeConstructorDecl → DtCD



/-! ## Declaring -/

namespace Datatype.Constructor.Decl

@[inherit_doc cvc5.TermManager.mkDatatypeConstructorDecl]
def mk (name : String) : Env Datatype.Constructor.Decl :=
  runUnsafe fun tm => tm.mkDatatypeConstructorDecl name

variable (d : Datatype.Constructor.Decl)

@[inherit_doc DtCD.addSelector]
def addSelector (name : String) (srt : Srt) : Env Datatype.Constructor.Decl :=
  runUnsafe' do d.toUnsafe.addSelector name srt.toUnsafe

/-- Adds a selector whose codomain is the datatype being declared. -/
def addSelectorSelf (name : String) : Env Datatype.Constructor.Decl :=
  runUnsafe' do d.toUnsafe.addSelectorSelf name

/-- Adds a selector whose codomain is another datatype of the same mutually recursive group. -/
def addSelectorUnresolved (name : String) (unresDatatypeName : String)
: Env Datatype.Constructor.Decl :=
  runUnsafe' do d.toUnsafe.addSelectorUnresolved name unresDatatypeName

end Datatype.Constructor.Decl

namespace Datatype.Decl

@[inherit_doc cvc5.TermManager.mkDatatypeDecl]
def mk (name : String) (params : Srts := #[]) (isCoDatatype : Bool := false) : Env Datatype.Decl :=
  runUnsafe fun tm => tm.mkDatatypeDecl name params isCoDatatype

variable (d : Datatype.Decl)

@[inherit_doc DtD.addConstructor]
def addConstructor (ctor : Datatype.Constructor.Decl) : Env Datatype.Decl :=
  runUnsafe' do d.toUnsafe.addConstructor ctor.toUnsafe

@[inherit_doc DtD.getNumConstructors]
def countConstructors : Nat := d.toUnsafe.getNumConstructors

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
def declareDatatype (s : Untyped.Solver) (symbol : String) (ctors : Array Datatype.Constructor.Decl)
: Env Srt := do
  let srt : Srt ←
    runUnsafe' do s.toUnsafe.declareDatatype symbol (ctors.map Datatype.Constructor.Decl.toUnsafe)
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

namespace Datatype.Constructor variable (c : Datatype.Constructor)

@[inherit_doc DtC.getName]
def getName : Res String := c.toUnsafe.getName

/-- The constructor term, the first argument of an `applyConstructor`. -/
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

instance : GetElem Datatype.Constructor Nat Datatype.Selector fun c idx => idx < c.countSelectors :=
  inferInstanceAs (GetElem DtC Nat DtS fun c idx => idx < c.getNumSelectors)

instance [Monad m] : ForIn m Datatype.Constructor Datatype.Selector :=
  inferInstanceAs (ForIn m DtC DtS)

end Datatype.Constructor

namespace Datatype variable (dt : Datatype)

@[inherit_doc Dt.getName]
def getName : Res String := dt.toUnsafe.getName

@[inherit_doc Dt.getConstructor]
def getConstructor (name : String) : Env Datatype.Constructor :=
  runUnsafe' do dt.toUnsafe.getConstructor name

@[inherit_doc Dt.getNumConstructors]
def countConstructors : Nat := dt.toUnsafe.getNumConstructors

@[inherit_doc Dt.getConstructorAt]
def getConstructorAt (idx : Fin dt.countConstructors) : Datatype.Constructor :=
  dt.toUnsafe.getConstructorAt idx

instance : GetElem Datatype Nat Datatype.Constructor fun dt idx => idx < dt.countConstructors :=
  inferInstanceAs (GetElem Dt Nat DtC fun dt idx => idx < dt.getNumConstructors)

instance [Monad m] : ForIn m Datatype Datatype.Constructor := inferInstanceAs (ForIn m Dt DtC)

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

Each of these takes the relevant term off a `Constructor` or `Selector` as its first argument,
which is how cvc5 spells datatype application.
-/

namespace Untyped.Term

/-- Applies a constructor to its arguments. -/
def applyConstructor (ctor : Term) (args : Terms := #[]) : Env Term :=
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
def ctorOf (t : Term) (name : String) : Env Datatype.Constructor := do
  let srt ← t.getSort
  if !srt.isDatatype then
    throwUser s!"cannot match on a term of sort `{srt}`, which is not a datatype"
  (← srt.getDatatype).getConstructor name

end Untyped.Term

namespace Datatype.Constructor variable (c : Datatype.Constructor)

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

end Datatype.Constructor

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
