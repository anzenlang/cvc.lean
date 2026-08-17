/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Sep
import Cvc.Typed.Core.Bool

public meta import Cvc.Typed.Theory.Sep
public meta import Cvc.Typed.Core.Bool



/-! # Separation logic, typed

`Heap α β` carries the location and data types, so the sort mismatch the sort-erased handle catches
at runtime is not expressible: `pto` takes a `Term α` and a `Term β`, and `nil` answers a
`Term α` with nothing to ascribe.

**The location sort is where this bites.** The natural choice for it is an *uninterpreted* sort,
and `Typ` has no case for one — `Srt.uninterpreted` builds a sort but no Lean type denotes it. So a
typed heap's locations have to be a type that `ToTyp` covers: `Int` here, or a declared datatype
through `Typ.datatype`. Sort-erased there is no such restriction, `Srt.uninterpreted` being an
ordinary sort. Closing this would mean giving `Typ` an `uninterpreted` case and registering the
sort as `Srt.datatype` already does.
-/
namespace Cvc.Tests.Typed.Term.Sep

open Cvc
open Cvc.Typed

/-- A solver ready for separation logic, over a heap of `Int` locations holding `Bool`s.

Two different types on purpose: at one type a mismatched `pto` would still typecheck.
-/
def solver [Ω] : Env Solver := do
  let s ← Solver.new
  s.setLogic Logic.all.qf
  -- separation logic is not supported incrementally
  s.setOption "incremental" "false"
  s.setOption "produce-models" "true"
  return s



/-! ## The indices the handle carries -/

section indices
variable [Ω] {s : Solver} (h : s.Heap Int Bool) (loc : Term Int) (data : Term Bool)

/-- Declaring answers a handle at the two types it was given. -/
example : Env (s.Heap Int Bool) := s.declareSepHeap Int Bool
/-- `nil` is a location, so it comes out at the location index. -/
example : Env (Term Int) := h.nil
/-- `pto` takes the heap's own indices, and answers a formula. -/
example : Term Int → Term Bool → Env (Term Bool) := h.pto
/-- The connectives mention no heap sort at all. -/
example : Env (Term Bool) := Term.sepEmp
example : Term Bool → Term Bool → Env (Term Bool) := Term.sepStar
example : Term Bool → Term Bool → Env (Term Bool) := Term.sepWand
end indices

/-! Swapping the operands is the mismatch the sort-erased layer reports at runtime. Here there is
nothing to report: `Term Bool` is not a `Term Int`. -/

/-- error: Application type mismatch: The argument
  data
has type
  Term Bool
but is expected to have type
  Term Int
in the application
  h.pto data

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs(error, drop info, drop warning) in
example [Ω] {s : Solver} (h : s.Heap Int Bool) (data : Term Bool) : Env (Term Bool) :=
  h.pto data data



/-! ## Building and solving -/

/-- info:
nil   : (as sep.nil Int)
pto   : (pto x v)
emp   : sep.emp
star  : (sep (pto x v) sep.emp)
wand  : (wand (pto x v) sep.emp)
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let h ← s.declareSepHeap Int Bool
  let x ← s.declareConst Int "x"
  let v ← s.declareConst Bool "v"

  let pto ← h.pto x v
  let emp ← Term.sepEmp
  println! "nil   : {← h.nil}"
  println! "pto   : {pto}"
  println! "emp   : {emp}"
  println! "star  : {← Term.sepStar pto emp}"
  println! "wand  : {← Term.sepWand pto emp}"

/-! `getValueSepHeap` and `getValueSepNil` answer formulas rather than values, so both are
`Term Bool` whatever the heap's indices — there is no index to carry across. -/

/-- info:
sat  : true
heap : (pto (- 1) true)
nil  : (= (as sep.nil Int) 0)
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let h ← s.declareSepHeap Int Bool
  let x ← s.declareConst Int "x"
  let v ← s.declareConst Bool "v"
  (h.pto x v) >>= s.assert

  s.checkSat (ifSat := do
    println! "sat  : true"
    println! "heap : {← s.getValueSepHeap}"
    println! "nil  : {← s.getValueSepNil}")

/-! ## The handle is a wrapper, not an abbreviation

`Heap` wraps the sort-erased handle in a `structure`. An abbreviation would unfold, and dot
notation would find `Untyped.Solver.Heap.pto` — which takes sort-erased terms and would *accept*
the typed ones, a typed term being definitionally its sort-erased one. The two `example`s above
pinning `h.pto`'s signature are what would catch that.
-/

/-! The sorts are still readable, and they are the ones the indices describe. -/

/-- info: sorts: (Int, Bool) -/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let h ← s.declareSepHeap Int Bool
  println! "sorts: {h.sorts}"
