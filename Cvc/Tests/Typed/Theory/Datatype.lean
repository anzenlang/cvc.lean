/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Datatype
import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Solver

public meta import Cvc.Typed.Theory.Datatype
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Solver



/-! # Datatypes, typed

A datatype sort is *declared*, and cvc5 makes a fresh one every time, so it cannot be rebuilt from
a description. Each declared sort is kept in the scope's registry under its name, and
`Typ.datatype` carries that name — so `ToTyp` can map a Lean index to a datatype and `Typ.toSrt`
looks it up instead of reconstructing it.

The consequence is that a datatype index is **first-class**: it goes wherever any other index goes.
-/
namespace Cvc.Tests.Typed.Datatype

open Cvc
open Cvc
open Cvc.Typed

/-- The Lean index standing for the SMT datatype `Pair`.

`Ord` because a `Set` keys its elements by it; nothing else about the index matters, since it
carries no data.
-/
structure Pair where private mk ::
  deriving DecidableEq, Ord, Hashable

instance : ToTyp Pair := ⟨.datatype "Pair"⟩

/-- Declares the datatype the `Pair` index names. -/
def declarePair [Ω] (s : Solver) : Env Srt := do
  let mk ← Cvc.Datatype.Constructor.Decl.mk "mk"
  let mk ← mk.addSelector "fst" (← Srt.int)
  let mk ← mk.addSelector "snd" (← Srt.bool)
  Untyped.Solver.declareDatatype s "Pair" #[mk]



/-! ## The index is first-class

This is what the registry buys, and what a handle-based design could not give: once declared, a
datatype index is accepted anywhere an index is.
-/

/-- info:
Srt.of Pair   : Pair
Set Pair      : (Set Pair)
Array Pair    : (Seq Pair)
Int → Pair    : (-> Int Pair)
Int × Pair    : (Tuple Int Pair)
declareConst  : p : Pair
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let _ ← declarePair s

  println! "Srt.of Pair   : {← (Srt.of Pair : Env Srt)}"
  println! "Set Pair      : {← (Srt.of (Cvc.Set Pair) : Env Srt)}"
  println! "Array Pair    : {← (Srt.of (Array Pair) : Env Srt)}"
  println! "Int → Pair    : {← (Srt.of (Int → Pair) : Env Srt)}"
  println! "Int × Pair    : {← (Srt.of (Int × Pair) : Env Srt)}"

  let p ← s.declareConst Pair "p"
  println! "declareConst  : {p.erase} : {← p.erase.getSort}"

-- naming a datatype before declaring it is an error, not a fresh incompatible sort
/-- info: undeclared : caught -/
#guard_msgs in #eval Env.runIO do
  let outcome ←
    try
      let _ ← (Srt.of Pair : Env Srt)
      pure "no error"
    catch _ => pure "caught"
  println! "undeclared : {outcome}"



/-! ## Building and taking apart values

`Datatype.ctor` and `Ctor.selector` take the *index*: no handle is threaded, because the sort is in
the registry. Which constructors exist and what sort each field has are runtime facts about the
declaration, so those two look their names up and check; from there the `Ctor α` and `Selector α β`
carry the indices and nothing else needs re-typing.
-/

/-- info:
value    : (mk 7 true)
fst      : (fst (mk 7 true))
is mk    : ((_ is mk) (mk 7 true))
updated  : ((_ update fst) (mk 7 true) 9)
model    : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let _ ← declarePair s

  let mkC ← Datatype.ctor Pair "mk"
  let fst ← mkC.field Int "fst"

  let p ← mkC.apply2 (← Term.mkInt 7) (← Term.mkTrue)
  println! "value    : {p.erase}"
  println! "fst      : {(← fst.get p).erase}"
  println! "is mk    : {(← mkC.is p).erase}"
  println! "updated  : {(← fst.update p (← Term.mkInt 9)).erase}"

  -- the indices are exact, so the model read needs no `typeCheck`
  let x ← s.declareConst Pair "x"
  (do Term.equal x p) >>= s.assert
  let xFst ← fst.get x
  s.checkSat (ifSat := do println! "model    : {← s.getValue xFst}")



/-! ## What the lookups check

A field's sort and a constructor's arity belong to the declaration, not to any index, so they are
checked where a name becomes a Lean type rather than left to cvc5.
-/

/-- info:
wrong field index : caught: selector `fst` of constructor `mk` has sort `Int`, not `Bool`
wrong arity       : caught: constructor `mk` takes 2 argument(s), got 0
wrong argument sort: caught: argument 0 of constructor `mk` should have sort `Int`, got `Bool`
not a datatype    : caught: sort `Int` is not a datatype
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let _ ← declarePair s
  let mkC ← Datatype.ctor Pair "mk"
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"

  println! "wrong field index : {← caught do let _ ← mkC.field Bool "fst"; pure "no error"}"
  println! "wrong arity       : {← caught do let _ ← mkC.apply; pure "no error"}"
  println! "wrong argument sort: \
{← caught do let _ ← mkC.apply2 (← Term.mkTrue) (← Term.mkTrue); pure "no error"}"
  println! "not a datatype    : {← caught do let _ ← Datatype.reflect Int; pure "no error"}"

-- and a wrong *index* is a type error, not a runtime one
section discipline
variable [Ω] (fst : Typed.Datatype.Field Pair Int) (p : Term Pair) (b : Term Bool)

/-- A selector answers at its own index. -/
example : Env (Term Int) := fst.get p

/-- info: @Datatype.Field.get : {α β : Type} → [inst : Ω] → Datatype.Field α β → Term α → Env (Term β) -/
#guard_msgs in #check @Cvc.Typed.Datatype.Field.get

/-- info: @Datatype.Ctor.is : {α : Type} → [inst : Ω] → Datatype.Ctor α → Term α → Env (Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Datatype.Ctor.is

end discipline



/-! ## Matching

A `Case α β` is one case of a match on a `Term α` whose bodies are `Term β`. The index says
statically what a sort-erased match only finds out at runtime — that every body agrees — while
coverage stays cvc5's to check, being a property of the declaration.

`Lst` is recursive, so it is declared with `Srt.datatype` rather than `Solver.declareDatatype`.
-/

/-- The Lean index standing for the SMT datatype `Lst`. -/
structure Lst where private mk ::
  deriving DecidableEq, Ord, Hashable

instance : ToTyp Lst := ⟨.datatype "Lst"⟩

/-- Declares the datatype the `Lst` index names. -/
def declareLst [Ω] : Env Srt := do
  let nil ← Cvc.Datatype.Constructor.Decl.mk "nil"
  let cons ← Cvc.Datatype.Constructor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Datatype.Decl.mk "Lst"
  Srt.datatype (← (← decl.addConstructor nil).addConstructor cons)

/-- info:
match     : (match l (((cons h t) h) (nil 0)))
head of l : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let _ ← declareLst

  let nilC ← Datatype.ctor Lst "nil"
  let consC ← Datatype.ctor Lst "cons"

  -- the head of `l`, or zero if it has none
  let h ← BVar.mk (α := Int) "h"
  let t ← BVar.mk (α := Lst) "t"
  let l ← s.declareConst Lst "l"
  let m ← Term.mkMatch l #[
    ← consC.case2 h t h.toTerm,
    ← nilC.case0 (← Term.mkInt 0),
  ]
  println! "match     : {m.erase}"

  -- `l` is a one-element list, so the match takes the `cons` branch
  let seven ← consC.apply2 (← Term.mkInt 7) (← nilC.apply)
  (do Term.equal l seven) >>= s.assert
  s.checkSat (ifSat := do println! "head of l : {← s.getValue m}")

/-! What a `Case` checks is what `Ctor.apply` checks: the constructor's arity, and the sorts of the
variables its fields are bound to.
-/

/-- info:
wrong arity     : caught: constructor `cons` takes 2 field(s), bound 1
wrong bound sort: caught: variable 0 bound by constructor `cons` should have sort `Int`, got `Lst`
-/
#guard_msgs in #eval Env.runIO do
  let _ ← declareLst
  let consC ← Datatype.ctor Lst "cons"
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"

  let h ← BVar.mk (α := Int) "h"
  let t ← BVar.mk (α := Lst) "t"
  println! "wrong arity     : {← caught do let _ ← consC.case1 h h.toTerm; pure "no error"}"
  println! "wrong bound sort: {← caught do let _ ← consC.case2 t h t.toTerm; pure "no error"}"

-- and bodies that disagree are a type error, not a runtime one
section discipline
variable [Ω] (intCase : Datatype.Case Lst Int) (boolCase : Datatype.Case Lst Bool) (l : Term Lst)

/-- A match answers at the index its cases share. -/
example : Env (Term Int) := Term.mkMatch l #[intCase, intCase]

/-- info: @Term.mkMatch : [inst : Ω] →
  {α β : Type} →
    Term α → (cases : Array (Datatype.Case α β)) → autoParam (0 < cases.size) Term.mkMatch._auto_1 → Env (Term β) -/
#guard_msgs in #check @Cvc.Typed.Term.mkMatch

/-- error: Application type mismatch: The argument
  boolCase
has type
  Datatype.Case Lst Bool
but is expected to have type
  Datatype.Case Lst Int
in the application
  List.cons boolCase
-/
#guard_msgs in example : Env (Term Int) := Term.mkMatch l #[intCase, boolCase]

end discipline
