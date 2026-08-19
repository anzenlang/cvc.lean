/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Datatype
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Theory.Datatype
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory



/-! # Datatypes, sort-erased -/
namespace Cvc.Tests.Untyped.Datatype

open Cvc Untyped



/-! ## Declaring, reflecting, and using

The full cycle on a one-constructor datatype: declare it, read it back out of its sort, build a
value with the constructor's term, and take it apart with a selector's.
-/

/-- info:
sort      : Pair, isDatatype true
name      : Pair, ctors 1
ctor      : mk, selectors 2
  sel     : fst : Int
  sel     : snd : Bool
value     : (mk 7 true)
fst       : (fst (mk 7 true))
is mk     : ((_ is mk) (mk 7 true))
updated   : ((_ update fst) (mk 7 true) 9)
model fst : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let mk ← Cvc.Datatype.Ctor.Decl.mk "mk"
  let mk ← mk.addSelector "fst" (← Srt.int)
  let mk ← mk.addSelector "snd" (← Srt.bool)
  let pair ← s.declareDatatype "Pair" #[mk]
  println! "sort      : {pair}, isDatatype {pair.isDatatype}"

  let dt ← pair.getDatatype
  println! "name      : {← dt.getName}, ctors {dt.countCtors}"
  let ctor ← dt.getCtorNamed "mk"
  println! "ctor      : {← ctor.getName}, selectors {ctor.countSelectors}"
  -- a constructor iterates over its selectors
  for sel in ctor do
    println! "  sel     : {← sel.getName} : {← sel.getCodomainSort}"

  let p ← Term.applyCtor (← ctor.getTerm) #[← Term.mkInt 7, ← Term.mkTrue]
  println! "value     : {p}"
  let fst ← ctor.getSelector "fst"
  println! "fst       : {← Term.applySelector (← fst.getTerm) p}"
  println! "is mk     : {← Term.applyTester (← ctor.getTesterTerm) p}"
  println! "updated   : {← Term.applyUpdater (← fst.getUpdaterTerm) p (← Term.mkInt 9)}"

  let x ← s.declareConst "x" pair
  (do Term.equal x p) >>= s.assert
  let xFst ← Term.applySelector (← fst.getTerm) x
  s.checkSat (ifSat := do println! "model fst : {← s.getValueAs Int xFst}")



/-! ## A name is declared once, and remembered

cvc5 makes a *fresh* sort every time a datatype is declared, even from an identical declaration,
and refuses to mix terms of two such sorts. This layer therefore keeps each declared sort in the
scope's registry, under its name, and rejects a second declaration of the same name rather than
silently producing an incompatible twin.

`Srt.ofName` is how the sort comes back, and it is what `Typ.toSrt` uses for a `Typ.datatype`.
-/

/-- info:
declared   : true
by name    : Pair
same sort  : true
undeclared : false
twice      : rejected
missing    : caught
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let declare : Env Srt := do
    let mk ← Cvc.Datatype.Ctor.Decl.mk "mk"
    let mk ← mk.addSelector "fst" (← Srt.int)
    s.declareDatatype "Pair" #[mk]

  let a ← declare
  println! "declared   : {← Srt.isDeclared "Pair"}"
  println! "by name    : {← Srt.ofName "Pair"}"
  -- the *same* sort comes back, which is what makes naming a datatype sound
  println! "same sort  : {a == (← Srt.ofName "Pair")}"
  println! "undeclared : {← Srt.isDeclared "Nope"}"

  let twice ←
    try
      let _ ← declare
      pure "accepted"
    catch _ => pure "rejected"
  println! "twice      : {twice}"

  let missing ←
    try
      let _ ← Srt.ofName "Nope"
      pure "no error"
    catch _ => pure "caught"
  println! "missing    : {missing}"



/-! ## Recursion

A datatype referring to itself uses `addSelectorSelf`, and needs the general `Srt.datatype` rather
than `Solver.declareDatatype`.
-/

/-- info:
sort   : Lst
ctors  : 2
value  : (cons 1 (cons 2 nil))
head   : (head (cons 1 (cons 2 nil)))
is nil : ((_ is nil) (cons 1 (cons 2 nil)))
-/
#guard_msgs in #eval Env.runIO do
  let nil ← Cvc.Datatype.Ctor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Ctor.Decl.mk "cons"
  let cons ← cons.addSelector "head" (← Srt.int)
  let cons ← cons.addSelectorSelf "tail"

  let decl ← Cvc.Datatype.Decl.mk "Lst"
  let decl ← decl.addCtor nil
  let decl ← decl.addCtor cons
  let lst ← Srt.datatype decl
  println! "sort   : {lst}"

  let dt ← lst.getDatatype
  println! "ctors  : {dt.countCtors}"
  let nilC ← dt.getCtorNamed "nil"
  let consC ← dt.getCtorNamed "cons"

  let nilT ← Term.applyCtor (← nilC.getTerm)
  let one ← Term.applyCtor (← consC.getTerm) #[← Term.mkInt 2, nilT]
  let two ← Term.applyCtor (← consC.getTerm) #[← Term.mkInt 1, one]
  println! "value  : {two}"
  println! "head   : {← Term.applySelector (← (← consC.getSelector "head").getTerm) two}"
  println! "is nil : {← Term.applyTester (← nilC.getTesterTerm) two}"



/-! ## Mutual recursion

Members of a group refer to each other by name through `addSelectorUnresolved`, and the names are
resolved only by `Srt.datatypes`, which declares the whole group at once.
-/

/-- info:
sorts : #[A, B]
A     : ctors 1, isWellFounded true
B     : ctors 2
value : (mkA (mkB (mkA stop)))
-/
#guard_msgs in #eval Env.runIO do
  let mkA ← Cvc.Datatype.Ctor.Decl.mk "mkA"
  let mkA ← mkA.addSelectorUnresolved "toB" "B"
  let declA ← Cvc.Datatype.Decl.mk "A"
  let declA ← declA.addCtor mkA

  let mkB ← Cvc.Datatype.Ctor.Decl.mk "mkB"
  let mkB ← mkB.addSelectorUnresolved "toA" "A"
  let stop ← Cvc.Datatype.Ctor.Decl.mk "stop"
  let declB ← Cvc.Datatype.Decl.mk "B"
  let declB ← declB.addCtor mkB
  let declB ← declB.addCtor stop

  let srts ← Srt.datatypes #[declA, declB]
  println! "sorts : {srts.map toString}"

  let some srtA := srts[0]? | throwUser "no first sort"
  let some srtB := srts[1]? | throwUser "no second sort"
  let dtA ← srtA.getDatatype
  let dtB ← srtB.getDatatype
  println! "A     : ctors {dtA.countCtors}, isWellFounded {dtA.isWellFounded}"
  println! "B     : ctors {dtB.countCtors}"

  let stopT ← Term.applyCtor (← (← dtB.getCtorNamed "stop").getTerm)
  let a ← Term.applyCtor (← (← dtA.getCtorNamed "mkA").getTerm) #[stopT]
  let b ← Term.applyCtor (← (← dtB.getCtorNamed "mkB").getTerm) #[a]
  let a2 ← Term.applyCtor (← (← dtA.getCtorNamed "mkA").getTerm) #[b]
  println! "value : {a2}"



/-! ## Predicates on a datatype -/

/-- info:
tuple is a datatype : true / isTuple true / isRecord false
plain datatype      : isTuple false / isParametric false / isCoDatatype false
finite              : true
-/
#guard_msgs in #eval Env.runIO do
  -- a tuple *is* a datatype, which is how its components will eventually be reached
  let tup ← Srt.tuple #[← Srt.int, ← Srt.bool]
  let tupDt ← tup.getDatatype
  println! "tuple is a datatype : {tup.isDatatype} / isTuple {tupDt.isTuple} / \
isRecord {tupDt.isRecord}"

  let s ← Solver.new
  let mk ← Cvc.Datatype.Ctor.Decl.mk "mk"
  let mk ← mk.addSelector "b" (← Srt.bool)
  let dt ← (← s.declareDatatype "Wrap" #[mk]).getDatatype
  println! "plain datatype      : isTuple {dt.isTuple} / isParametric {dt.isParametric} / \
isCoDatatype {dt.isCoDatatype}"
  println! "finite              : {← dt.isFinite}"



/-! ## Matching

A match picks a body by the constructor its scrutinee was built with. A constructor taking fields
binds them to bound variables, which is all the binding a match needs — no quantifier is involved.
-/

/-- info:
match     : (match l (((cons h t) h) (nil 0)))
sort      : Int
head of l : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let nil ← Cvc.Datatype.Ctor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Ctor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Datatype.Decl.mk "Lst"
  let lst ← Srt.datatype (← (← decl.addCtor nil).addCtor cons)
  let dt ← lst.getDatatype
  let nilC ← dt.getCtorNamed "nil"
  let consC ← dt.getCtorNamed "cons"

  -- the head of `l`, or zero if it has none
  let l ← s.declareConst "l" lst
  let h ← BVar.mk (← Srt.int) "h"
  let t ← BVar.mk lst "t"
  let consCase ←
    Term.matchBindCase #[h, t] (← Term.applyCtor (← consC.getTerm) #[h, t]) h
  let nilCase ←
    Term.matchCase (← Term.applyCtor (← nilC.getTerm)) (← Term.mkInt 0)
  let m ← Term.mkMatch l #[consCase, nilCase]
  println! "match     : {m}"
  println! "sort      : {← m.getSort}"

  -- `l` is a one-element list, so the match takes the `cons` branch
  let nilT ← Term.applyCtor (← nilC.getTerm)
  let seven ← Term.applyCtor (← consC.getTerm) #[← Term.mkInt 7, nilT]
  (do Term.equal l seven) >>= s.assert
  s.checkSat (ifSat := do println! "head of l : {← s.getValueAs Int m}")

/-! A case whose pattern is a lone bound variable matches whatever the earlier ones left over, and
is how a match covers the constructors it does not name. Coverage and agreement between the bodies
are cvc5's to check, both being properties of the datatype's declaration.
-/

/-- info:
catch-all : (match l (((cons h t) h) (x 0)))
partial   : [internal] cases for match term are not exhaustive
mixed     : [internal] incomparable types in match case list
true: Bool
expected: Int
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let nil ← Cvc.Datatype.Ctor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Ctor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Datatype.Decl.mk "Lst"
  let lst ← Srt.datatype (← (← decl.addCtor nil).addCtor cons)
  let dt ← lst.getDatatype
  let consC ← dt.getCtorNamed "cons"
  let l ← s.declareConst "l" lst

  let h ← BVar.mk (← Srt.int) "h"
  let t ← BVar.mk lst "t"
  let consCase ←
    Term.matchBindCase #[h, t] (← Term.applyCtor (← consC.getTerm) #[h, t]) h

  let x ← BVar.mk lst "x"
  let anyCase ← Term.matchBindCase #[x] x (← Term.mkInt 0)
  println! "catch-all : {← Term.mkMatch l #[consCase, anyCase]}"

  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"
  println! "partial   : {← caught do pure s!"{← Term.mkMatch l #[consCase]}"}"
  let boolCase ←
    Term.matchCase (← Term.applyCtor (← (← dt.getCtorNamed "nil").getTerm))
      (← Term.mkTrue)
  println! "mixed     : {← caught do pure s!"{← Term.mkMatch l #[consCase, boolCase]}"}"


/-! # The `smt!` DSL's `match`

`match … with` is declared and expanded in this theory's own module, so it exists exactly where
datatypes do — importing another theory alone leaves it out of the grammar, and `smt! match …`
does not parse. Its tests belong here for the same reason.
-/

/-! ## Matching

`match … with` binds each constructor's fields for the writer, so a match reads the way Lean's
does and no bound variable has to be made by hand. The printed term shows the variables under the
names they were written with.

The catch-all is `_`. A bare identifier is always a constructor name, so `| nil => …` is the
nullary constructor and not a variable.
-/

/-- Declares a recursive list of integers, `nil | cons (head : Int) (tail : Lst)`. -/
def declareLst [Ω] : Env Srt := do
  let nil ← Cvc.Datatype.Ctor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Ctor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Datatype.Decl.mk "Lst"
  Srt.datatype (← (← decl.addCtor nil).addCtor cons)

/-- info:
match     : (match l (((cons h t) h) (nil 0)))
head of l : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let lst ← declareLst
  let l ← s.declareConst "l" lst

  let m ← smt!
    match l with
    | cons h t => h
    | nil => 0
  println! "match     : {m}"

  -- `l` is a one-element list, so the match takes the `cons` branch
  let dt ← lst.getDatatype
  let nilT ← Term.applyCtor (← (← dt.getCtorNamed "nil").getTerm)
  let seven ← Term.applyCtor (← (← dt.getCtorNamed "cons").getTerm)
    #[← Term.mkInt 7, nilT]
  (do Term.equal l seven) >>= s.assert
  s.checkSat (ifSat := do println! "head of l : {← s.getValueAs Int m}")

/-! A bound variable is an ordinary term in the body, so the operators and the rest of the DSL
apply to it — including a nested `match` on a field of the same datatype.
-/

/-- info:
arithmetic : (match l (((cons h t) (+ (* h 2) 1)) (nil 0)))
catch-all  : (match l (((cons h t) h) (_ 0)))
nested     : (match l (((cons h t) (match t (((cons h t) h) (_ 0)))) (_ 0)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let l ← s.declareConst "l" (← declareLst)

  println! "arithmetic : {← smt!
    match l with
    | cons h t => h * 2 + 1
    | nil => 0}"

  println! "catch-all  : {← smt!
    match l with
    | cons h t => h
    | _ => 0}"

  println! "nested     : {← smt!
    match l with
    | cons h t =>
      match t with
      | cons h t => h
      | _ => 0
    | _ => 0}"

/-! What the expansion checks, and what it leaves to cvc5. -/

/-- info:
unknown ctor : [internal] no constructor snoc for datatype Lst exists, among { nil cons }
wrong width  : constructor `cons` takes 2 field(s), bound 1
not datatype : cannot match on a term of sort `Int`, which is not a datatype
non-exhaustive: [internal] cases for match term are not exhaustive
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let l ← s.declareConst "l" (← declareLst)
  let i ← s.declareConst "i" (← Srt.int)
  let caught (code : Env String) : Env String := try code catch e => pure s!"{e}"

  println! "unknown ctor : {← caught do pure s!"{← smt! match l with | snoc h t => h}"}"
  println! "wrong width  : {← caught do pure s!"{← smt! match l with | cons h => h}"}"
  println! "not datatype : {← caught do pure s!"{← smt! match i with | cons h t => h}"}"
  println! "non-exhaustive: {← caught do pure s!"{← smt! match l with | cons h t => h}"}"

/-! What the *expansion* rejects, before anything is built. -/

section rejected
variable [Ω] (l : Term)

/-- error:
a sort ascription has no meaning in the sort-erased layer, where a field's sort comes from the
datatype's declaration
-/
#guard_msgs in example : Env Term := smt! match l with | cons h (t : Nat) => h

end rejected

/-! ## Hygiene

A pattern binds under the name it was written with and nothing else. The expansion's own names are
macro-scoped, so they cannot capture one, and a pattern variable shadows an outer binding only
inside its own body.
-/

-- the Lean name `h` is bound outside to a constant printing as `outerH`, so the `cons` body
-- showing `h` is the pattern's variable and the catch-all showing `outerH` is the outer one
/-- info:
shadowing : (match l (((cons h t) h) (_ outerH)))
outer     : outerH
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let l ← s.declareConst "l" (← declareLst)
  let h ← s.declareConst "outerH" (← Srt.int)
  println! "shadowing : {← smt!
    match l with
    | cons h t => h
    | _ => ![pure h]}"
  println! "outer     : {h}"
