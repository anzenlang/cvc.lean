/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Sep
import Cvc.Untyped.Core.Bool

public meta import Cvc.Untyped.Theory.Sep
public meta import Cvc.Untyped.Core.Bool



/-! # Separation logic, sort-erased

The heap is solver state, so the two constructors that mention its sorts — `pto` and `nil` — come
off the handle `declareSepHeap` answers, and the handle checks them. `emp`, `sep` and `wand`
mention no heap sort and are ordinary generated constructors.

What the handle buys is checked below: cvc5 accepts a mismatched `pto` at construction and rejects
it at check-sat, with an error about `set.union` naming neither `pto` nor the heap. The handle
turns that into a message naming both operand and sort.
-/
namespace Cvc.Tests.Untyped.Term.Sep

open Cvc
open Cvc.Untyped

/-- A solver ready for separation logic, over a heap of `Loc` locations holding `Int`s. -/
def solver [Ω] : Env (Solver × Srt × Srt) := do
  let s ← Solver.new
  s.setLogic Logic.all.qf
  -- separation logic is not supported incrementally
  s.setOption "incremental" "false"
  s.setOption "produce-models" "true"
  let loc ← Srt.uninterpreted "Loc"
  let int ← Srt.int
  return (s, loc, int)



/-! ## Building -/

/-- info:
nil   : (as sep.nil Loc)
pto   : (pto x v)
emp   : sep.emp
star  : (sep (pto x v) sep.emp)
wand  : (wand (pto x v) sep.emp)
starN : (let ((_let_1 (pto x v))) (sep _let_1 sep.emp _let_1))
-/
#guard_msgs in #eval Env.runIO do
  let (s, loc, int) ← solver
  let h ← s.declareSepHeap loc int
  let x ← s.declareConst "x" loc
  let v ← s.declareConst "v" int

  let pto ← h.pto x v
  let emp ← Term.sepEmp
  println! "nil   : {← h.nil}"
  println! "pto   : {pto}"
  println! "emp   : {emp}"
  println! "star  : {← Term.sepStar pto emp}"
  println! "wand  : {← Term.sepWand pto emp}"
  println! "starN : {← Term.sepStarN #[pto, emp, pto]}"

/-! ## What the handle checks

Both of these build without complaint in cvc5 and fail only at check-sat, as
`Operator set.union expects two sets of comparable type`.
-/

/-- info:
wrong location : caught: this heap's locations have sort `Loc`, but `v` has sort `Int`
wrong data     : caught: this heap's data has sort `Int`, but `x` has sort `Loc`
-/
#guard_msgs in #eval Env.runIO do
  let (s, loc, int) ← solver
  let h ← s.declareSepHeap loc int
  let x ← s.declareConst "x" loc
  let v ← s.declareConst "v" int
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"

  println! "wrong location : {← caught do pure s!"{← h.pto v v}"}"
  println! "wrong data     : {← caught do pure s!"{← h.pto x x}"}"

/-! `nil` needs no check: it is built at the heap's own location sort rather than at one the caller
names, so cvc5's `mkSepNil`, which takes any sort at all, cannot be reached with the wrong one. -/

/-- info: nil sort: Loc -/
#guard_msgs in #eval Env.runIO do
  let (s, loc, int) ← solver
  let h ← s.declareSepHeap loc int
  println! "nil sort: {← (← h.nil).getSort}"

/-! ## Solving, and reading the heap back

`getValueSepHeap` and `getValueSepNil` answer `Bool`-sorted *formulas* characterizing the model,
not values — which is why both are plain terms whatever the heap's sorts.
-/

/-- info:
sat  : true
heap : (pto (as @Loc_0 Loc) 0)
nil  : (= (as sep.nil Loc) (as @Loc_1 Loc))
-/
#guard_msgs in #eval Env.runIO do
  let (s, loc, int) ← solver
  let h ← s.declareSepHeap loc int
  let x ← s.declareConst "x" loc
  let v ← s.declareConst "v" int
  (h.pto x v) >>= s.assert

  s.checkSat (ifSat := do
    println! "sat  : true"
    println! "heap : {← s.getValueSepHeap}"
    println! "nil  : {← s.getValueSepNil}")

/-! ## What is left to cvc5, and what the handle removes

cvc5 rejects a second `declareSepHeap` on one solver, and that stays a runtime check: how many
times a function has been called is not something a type here can say.

Its *other* condition — a separation-logic constraint against a heap that was never declared, which
it reports at check-sat — becomes unreachable. `pto` and `nil` exist only on a `Heap`, and the only
way to a `Heap` is `declareSepHeap`, so a constraint that has not been through it cannot be built.
-/

/-- info: declared twice : caught -/
#guard_msgs in #eval Env.runIO do
  let (s, loc, int) ← solver
  let _ ← s.declareSepHeap loc int
  let caught (code : Env String) : Env String := try code catch _ => pure "caught"

  println! "declared twice : {← caught do let _ ← s.declareSepHeap int loc; pure "no error"}"

/-! ## A handle belongs to its solver

Two solvers sharing a scope may declare *different* heaps — cvc5 allows it, so a location of one
is not a location of the other. `Heap` is indexed by its solver for that reason, which is what
keeps the two apart.
-/

/-- Declaring answers a handle indexed by *that* solver, and it is the only source of one. -/
example [Ω] (s : Solver) : Srt → Srt → Env (Solver.Heap s) := s.declareSepHeap

/-- So the operations are reached through the solver that owns them. -/
example [Ω] (s : Solver) (h : Solver.Heap s) (x v : Term) : Env Term := h.pto x v
