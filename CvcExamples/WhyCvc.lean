module

import Cvc



namespace Why.CvcLean



/-! # `lean-cvc5`

`lean-cvc5` is a low-level API on top of cvc5's C++ API: it gives you lean versions of cvc5's C++
types and functions/methods and (almost) nothing else.
-/
namespace lean_cvc5
open cvc5

def demo : Env Unit := do
  -- the term manager perfect-shares sorts and terms
  let tm ← TermManager.new

  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort

  let zero ← tm.mkInteger 0
  let b1 ← tm.mkConst bool "b1"
  let i1 ← tm.mkConst int "i1"

  -- `0 < i1`
  let zero_lt_i1 ← tm.mkTerm .LT #[zero, i1]
  -- `b1 ∧ 0 < i1`
  let term ← tm.mkTerm .AND #[b1, zero_lt_i1]

  let solver ← Solver.new tm
  solver.setOption "produce-models" "true"
  solver.assertFormula term

  let satRes ← solver.checkSat
  if satRes.isSat then
    let b1Val ← solver.getValue b1
    let i1Val ← solver.getValue i1
    println! "sat: b1 := {b1Val}, i1 := {i1Val}"
  else if satRes.isUnsat then
    println! "unsat 🙀"
  else println! "unknown"

/-- info:
sat: b1 := true, i1 := 1
-/
#guard_msgs in #eval Env.runIO demo

end lean_cvc5



/-!
This is definitely useable but leaves a lot of room for errors that will only appear at runtime
- internally ill-typed terms
- ill-typed SMT queries, *e.g.* asserting a term of sort `Int`
- invalid solver queries, *e.g.* asking for values after an unsat result



# `cvc.lean`

`cvc.lean` adds bells, whistles, and safety on top of `lean-cvc5`.

## `Untyped`

Its `Env` environment encodes the following:
- trying to use a term/sort/... after its term manager was freed fails at compile-time
- mixing terms from different managers is a type error

It provides a function per term constructor (sometimes several) for ergonomics.

Invalid solver queries are rejected at compile-time.
-/

namespace cvc_lean_untyped
open Cvc Untyped

variable [Ω]

def demo : Env Unit := do
  let bool ← Srt.bool
  let int ← Srt.int

  let zero ← Term.mkInt 0
  let b1 ← Term.mkSymbol bool "b1"
  let i1 ← Term.mkSymbol int "i1"

  -- `0 < i1`
  let zero_lt_i1 ← zero.lt i1
  -- `b1 ∧ 0 < i1`
  let _ ← b1.and zero_lt_i1

  -- alternatively, using the `smt!` syntax extension
  let term ← smt! b1 ∧ 0 < i1

  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  solver.assert term

  solver.checkSat
    (ifSat := do
      let b1Val ← solver.getValue b1
      let i1Val ← solver.getValue i1
      println! "sat: b1 := {b1Val}, i1 := {i1Val}")
    (ifUnsat := throwUser "unsat 🙀")
    (ifUnknown := fun reason => throwUser s!"unknown: {reason}")

/-- info:
sat: b1 := true, i1 := 1
-/
#guard_msgs in #eval Env.runIO demo

end cvc_lean_untyped


/-! ## Typed

The typed API adds even more on top of `Untyped`, most importantly **strongly-typed terms**.
-/

namespace cvc_lean_typed
open Cvc Typed

variable [Ω]

def demo : Env Unit := do
  let b1 ← Term.mkSymbol "b1"
  let i1 ← Term.mkSymbol "i1"
  -- `b1 : Term Bool` and `i1 : Term Int`, inferred from usage in `term` below
  -- `Typed` has the `smt!` extension too
  let term ← smt! b1 ∧ 0 < i1

  -- as an aside, strong-typing and `smt!` work with function application too
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  let partialApp ← smt! f i1
  let _totalApp ← smt! partialApp term

  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  solver.assert term

  let (b1Val, i1Val) ← solver.checkSat
    (ifSat := do
      let b1Val ← solver.getValueTerm b1
      let i1Val ← solver.getValueTerm i1
      return (b1Val, i1Val))
    (ifUnsat := throwUser "unsat 🙀")
    (ifUnknown := fun reason => throwUser s!"unknown: {reason}")
  println! "sat: b1 := {b1Val}, i1 := {i1Val}"

  let different_i1 ← smt! i1 ≠ i1Val
  -- not specifying some of the branches causes them to fail with `"unexpected result ..."`
  solver.checkSat
    (assuming := #[different_i1])
    (ifSat := do
      let b1Val ← solver.getValue b1
      let i1Val ← solver.getValue i1
      println! "sat: b1 := {b1Val}, i1 := {i1Val}")

/--
info:
sat: b1 := true, i1 := 1
sat: b1 := true, i1 := 2
-/
#guard_msgs in #eval Env.runIO demo

end cvc_lean_typed

/-! # Manual

Make sure to browse the user manual for much, much more:
- https://www.anzenlang.io/cvc.lean/manual/
-/
