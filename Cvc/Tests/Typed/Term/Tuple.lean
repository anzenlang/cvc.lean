/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Term
import Cvc.Typed.Solver

public meta import Cvc.Typed.Term
public meta import Cvc.Typed.Solver



/-! # Tuples, typed -/
namespace Cvc.Tests.Typed.Term.Tuple

open Cvc
open Cvc
open Cvc.Typed



/-! ## The index says what the sort is

A product index flattens to the right, so `α × β × γ` is one three-component tuple. Each line below
prints the sort the term actually has beside the sort its index claims; the two agreeing is the
whole point of the constructor's shape.
-/

/-- info:
pair   : (Tuple Int Bool) / (Tuple Int Bool)
triple : (Tuple Int Bool Real) / (Tuple Int Bool Real)
quad   : (Tuple Int Bool Real Int) / (Tuple Int Bool Real Int)
nested : (Tuple (Tuple Int Bool) Real) / (Tuple (Tuple Int Bool) Real)
-/
#guard_msgs in #eval Env.runIO do
  let one ← Term.mkInt 1
  let tru ← Term.mkTrue
  let half ← Term.mkReal (1/2 : Rat)

  let pair ← Term.mkTuple one (.last tru)
  println! "pair   : {← pair.erase.getSort} / {← (Srt.of (Int × Bool) : Env Srt)}"

  let triple ← Term.mkTuple one (.cons tru (.last half))
  println! "triple : {← triple.erase.getSort} / {← (Srt.of (Int × Bool × Rat) : Env Srt)}"

  let quad ← Term.mkTuple one (.cons tru (.cons half (.last one)))
  println! "quad   : {← quad.erase.getSort} / {← (Srt.of (Int × Bool × Rat × Int) : Env Srt)}"

  -- a tuple *does* nest, to the left, and that index is exact too
  let nested ← Term.mkTuple pair (.last half)
  println! "nested : {← nested.erase.getSort} / {← (Srt.of ((Int × Bool) × Rat) : Env Srt)}"



/-! ## What the last component may be

`cons` takes any component, including a tuple, because a tuple there nests. `last` does not: a
product index would flatten its own components into the tuple being built, while the single term
it stands for would not, and the index would then lie about the sort.
-/

section discipline
variable [Ω] (i : Term Int) (b : Term Bool) (r : Term Rat) (p : Term (Bool × Rat))

/-- Any flat index ends a tuple. -/
example : Env (Term (Int × Bool)) := Term.mkTuple i (.last b)

/-- A container index is flat — only a *product* is not. -/
example (s : Term (Cvc.Set Int)) : Env (Term (Int × Cvc.Set Int)) :=
  Term.mkTuple i (.last s)

/-- A function index likewise. -/
example (f : Term (Int → Bool)) : Env (Term (Int × (Int → Bool))) := Term.mkTuple i (.last f)

/-- A tuple is fine anywhere but last, where it nests to the left. -/
example : Env (Term ((Bool × Rat) × Int)) := Term.mkTuple p (.last i)

/-- …and as an inner component. -/
example : Env (Term (Int × (Bool × Rat) × Int)) := Term.mkTuple i (.cons p (.last i))

/-- info: @Term.mkTuple : [inst : Ω] → {α β : Type} → [ToTyp α] → Term α → Term.Components β → Env (Term (α × β)) -/
#guard_msgs in #check @Cvc.Typed.Term.mkTuple

end discipline

-- and the rejection is a *type* error, not a runtime one: a product cannot end a tuple
/--
error: could not synthesize default value for parameter '_isFlat' using tactics
---
error: a tuple's last component cannot itself be a tuple: its components would flatten into the tuple being built. Nest to the left instead.
inst✝ : Ω
i : Term Int
p : Term (Bool × Rat)
⊢ False
-/
#guard_msgs in
example [Ω] (i : Term Int) (p : Term (Bool × Rat)) : Env (Term (Int × (Bool × Rat))) :=
  Term.mkTuple i (.last p)



/-! ## Projection and values

Both are sort-erased in their result: which components an index array selects is a runtime value,
and a tuple's components have as many indices as it has components.
-/

/-- info:
project : (Tuple Real Int)
isValue : true
values  : #[1, true, (/ 1 2)]
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple (← Term.mkInt 1)
    (.cons (← Term.mkTrue) (.last (← Term.mkReal (1/2 : Rat))))
  println! "project : {← (← Term.tupleProject #[2, 0] triple).getSort}"
  println! "isValue : {triple.isTupleValue}"
  println! "values  : {(← triple.getTupleValue).map toString}"



/-! ## End to end -/

/-- info: x = 4 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← s.declareConst Int "x"
  let lft ← Term.mkTuple x (.last (← Term.mkTrue))
  let rgt ← Term.mkTuple (← Term.mkInt 4) (.last (← Term.mkTrue))
  (do Term.equal lft rgt) >>= s.assert

  s.checkSat (ifSat := do println! "x = {← s.getValue x}")



/-! ## Selection

`fst` and `snd` read a tuple as Lean's `Prod.fst`/`Prod.snd` read a product. That is what lets them
work at every arity: `snd` of an `α × β × γ` is the *tuple* `(Tuple β γ)`, exactly as Lean's `snd`
of `α × (β × γ)` is the pair — never component 1 on its own.

Each line below prints the sort the term has beside the sort its index claims. The two agreeing at
every arity is the whole point.
-/

/-- info:
pair.fst   : Int / Int
pair.snd   : Bool / Bool
triple.fst : Int / Int
triple.snd : (Tuple Bool String) / (Tuple Bool String)
quad.snd   : (Tuple Bool String Int) / (Tuple Bool String Int)
nested.fst : (Tuple Int Bool) / (Tuple Int Bool)
nested.snd : String / String
-/
#guard_msgs in #eval Env.runIO do
  let one ← Term.mkInt 1
  let tru ← Term.mkTrue
  let str ← Term.mkString "s" false

  let pair : Term (Int × Bool) ← Term.mkTuple one (.last tru)
  let triple : Term (Int × Bool × String) ← Term.mkTuple one (.cons tru (.last str))
  let quad : Term (Int × Bool × String × Int) ←
    Term.mkTuple one (.cons tru (.cons str (.last one)))
  -- a tuple nests to the *left*, so here the first component is itself a tuple
  let nested : Term ((Int × Bool) × String) ← Term.mkTuple pair (.last str)

  let show! (label : String) (got : Untyped.Term) (claimed : Env Srt) : Env Unit := do
    println! "{label} : {← got.getSort} / {← claimed}"

  show! "pair.fst  " (← pair.fst).erase (Srt.of Int)
  show! "pair.snd  " (← pair.snd).erase (Srt.of Bool)
  show! "triple.fst" (← triple.fst).erase (Srt.of Int)
  show! "triple.snd" (← triple.snd).erase (Srt.of (Bool × String))
  show! "quad.snd  " (← quad.snd).erase (Srt.of (Bool × String × Int))
  show! "nested.fst" (← nested.fst).erase (Srt.of (Int × Bool))
  show! "nested.snd" (← nested.snd).erase (Srt.of String)

/-! On a longer tuple `snd` rebuilds the tail from its components rather than projecting it. The
two are the same term to the solver, which is what this checks.
-/

/-- info: snd = tupleProject #[1, 2] : unsat -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let x ← s.declareConst (Int × Bool × String) "x"
  let viaSnd ← x.snd
  let viaProject ← Untyped.Term.tupleProject #[1, 2] x.erase
  let same ← Untyped.Term.equal viaSnd.erase viaProject
  (do Untyped.Term.not same) >>= Untyped.Solver.assert s
  println! "snd = tupleProject #[1, 2] : {if ← Untyped.Solver.checkIsSat s then "SAT" else "unsat"}"

/-! Both read back off a *symbolic* tuple, which is what distinguishes them from `getTupleValue`:
they build terms rather than decoding a value.
-/

/-- info:
fst : 9
snd : false
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst (Int × Bool) "x"
  (do Term.equal x (← Term.mkTuple (← Term.mkInt 9) (.last (← Term.mkFalse)))) >>= s.assert
  let first ← x.fst
  let second ← x.snd
  s.checkSat (ifSat := do
    println! "fst : {← s.getValue first}"
    println! "snd : {← s.getValue second}")

section indices
variable [Ω] (pair : Term (Int × Bool)) (triple : Term (Int × Bool × String))

/-- `fst` answers the first factor. -/
example : Env (Term Int) := pair.fst
/-- On a pair, `snd` answers the second. -/
example : Env (Term Bool) := pair.snd
/-- On a longer tuple it answers the tail, as a tuple. -/
example : Env (Term (Bool × String)) := triple.snd
/-- …so it composes: the tail of the tail. -/
example : Env (Term String) := do (← triple.snd).snd

/-- info: @Term.snd : [inst : Ω] → {β α : Type} → [B : ToTyp β] → Term (α × β) → Env (Term β) -/
#guard_msgs in #check @Cvc.Typed.Term.snd

end indices
