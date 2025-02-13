/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe



/-! # Welcome

## Abstract

The [cvc5] SMT solver is a state-of-art constraint solver used in a wide
array of automatic formal verification use cases. Such solvers often expose their APIs in various
programming language so that developers can easily implement constraint solving in specific
contexts, in particular static analyzers for a certain language or kind of programs. Exposing a
clean, ergonomic API is crucial as SMT solvers are relatively technical tools to use correctly.

This talk discusses [cvc.lean], a public-but-not-released-yet [Lean 4] library developed with the
University of Iowa and the cvc5 team. It exposes a powerful and *safe* version of the cvc5's API:
strongly-typed terms and interactions with the backend solver, an `smt!` syntax extension to easily
and idiomatically write SMT terms as logical formulas. Combined with cvc5's powerful features (which
go beyond usual [SMT-LIB] commands), cvc.lean lets users write complex constraint-solving code in a
concise and (lean-)idiomatic way, while preventing a lot of the pitfalls of using SMT-solvers by
checking that cvc5 terms and functions are used correctly at compile time.

[cvc5]: https://cvc5.github.io
[cvc.lean]: https://github.com/anzenlang/cvc.lean
[Lean 4]: https://lean-lang.org
[SMT-LIB]: https://smt-lib.org
-/
namespace Demo

open Lean (RBMap)

/-- We will need to map identifiers (`String`s) to some types. -/
abbrev SymbolMap (α : Type) :=
  RBMap String α compare

namespace SymbolMap
def empty : SymbolMap α := RBMap.empty

def ofList (l : List (String × α)) : SymbolMap α := Id.run do
  let mut map := empty
  for (key, val) in l do
    map := map.insert key val
  return map
end SymbolMap



namespace adhoc

open Cvc

namespace Trash
/-! Consider this function. -/

def f (n1 : Int) (n2 : Int) (n3 : Int) (flag : Bool) : Int :=
  n1 - 2 * n2 + (
    if flag
    then 3 * (n3 - n1 + n2)
    else 4 * (n1 - n3)
  )

/-! Also consider these `constraints` over `f`'s inputs. -/

def constraints (n1 : Int) (n2 : Int) (n3 : Int) (flag : Bool) : Bool :=
    -10 ≤ n1 ∧ n1 ≤ 10
  ∧ -10 ≤ n2 ∧ n2 ≤ 10
  ∧  -5 ≤ n3 ∧ n3 ≤  5
  ∧ ( 0 < n2 → flag )

/-!
Is there a valuation `vals` of `f`'s inputs that verifies some condition `c (f vals)`?

- if there is, return the value `f vals` and `vals` itself.
-/

end Trash

/-!
Let's solve this problem with cvc5 and `cvc.lean`. (Or at least *pretend to* for now.)
-/

/-- info: Cvc.Term : Type -/
#guard_msgs(info) in
#check Term

/-!
So the result we want is `Option (Term × SymbolMap Term)`:

- `Option` because the domain might be empty (yielding `none`)

- the first `Cvc.Term` is the (term) *value* of `f` verifying the constraints

- the `SymbolMap` gives (term) *value* to identifiers

  (here: `"n1"`, `"n2"`, `"n3"`, and `"flag"`)
-/

/-- info: Cvc.SmtM (α : Type) : Type -/
#guard_msgs(info) in
#check SmtM

open Smt in

/-- warning: declaration uses 'sorry' -/
#guard_msgs(warning) in

def adHocMinimizeSmt (c : Term → SmtM Term) : SmtM (Option (Term × SymbolMap Term)) := do
  -- don't forget to set the options we need, *model production* here
  setOption .produceModels

  -- set the logic we need to express `f` and our constraints
  setLogic .qf_lia

  -- build the `Cvc.Srt` values for the sorts (types) we need
  let int ← Srt.int
  let bool ← Srt.bool

  -- declare our function symbols (variables)
  let n1 ← declareFun' "n1" #[] int
  -- [...] same for the other variables

  -- use the cvc5 term factory to build relevant terms
  let cst_m10 ← Term.mkInt (-10)
  let cst_10 ← Term.mkInt 10
  -- [...] *etc.*

  -- assert our constraints
  Smt.assert (← cst_m10.le n1) -- `-10 ≤ n1`
  Smt.assert (← n1.le cst_10)  --       `n1 ≤ 10`
  -- [...] same for the other constraints

  -- build the term corresponding to the function we're analyzing so that we can build `c f`
  let f : Term ← do
    sorry -- more tedious `Term` factory invocations

  -- ready to build and assert the condition now
  let condition ← c f
  assert condition

  -- just ask cvc5
  match ← checkSat? with
  | none =>
    -- cvc5 could not decide (timeout/gave up), only on big problem or in complex logics
    throw (Error.internal "solver failed to answer check-sat command")
  | some true =>
    -- cvc5 found a solution, we must retrieve the values we need
    let mut vals := SymbolMap.empty
    vals := vals.insert "n1" (← getValue n1)
    -- [...] same for the other variables
    let fVal ← getValue f
    return (fVal, vals)
  | some false =>
    -- cvc5 proved there is no `vals` such that `c (f vals)` is true
    return none

end adhoc



/-! That was terrible, let's use `cvc.lean` QoL helpers. -/
namespace adhoc2

open Cvc
open scoped Cvc.Term

open Smt in

def adHocMinimizeSmt
  (c : Term → SmtM Term)
: SmtM (Option (Term × SymbolMap Term)) := do
  setOption .produceModels
  setLogic .qf_lia
  -- first off, `cvc.lean` lets us use appropriate lean types to avoid `Str.int` *etc.*
  let n1 ← declareFun "n1" Int
  let n2 ← declareFun "n2" Int
  let n3 ← declareFun "n3" Int
  let flag ← declareFun "flag" Bool
  -- -- works with functions too!
  -- let unknownFunction ← declareFun "unknownFunction" (Int → Bool → Int)

  -- using a term factory is tedious, so `cvc.lean` has syntax extensions to write terms in a
  -- (lean-)idiomatic fashion
  let constraints ← smt!
    (-10) ≤ n1 ∧ n1 ≤ 10 ∧
    (-10) ≤ n2 ∧ n2 ≤ 10 ∧
    (- 5) ≤ n3 ∧ n3 ≤  5 ∧
    (0 ≤ n2 → flag)
    -- -- also works with functions with lean-like syntax for application!
    -- ∧ unknownFunction n3 flag ≤ 7
  assert constraints

  -- `f`'s definition is nice and readable now
  let f ←
    smt! n1 - 2 * n2 + (if flag then (3 * (n3 + n1 - n2)) else (4 * (n1 - n3)))

  assert (← c f)

  match ← checkSat? with

  | none =>
    -- cvc5 could not decide (timeout/gave up), only on big problem or in complex logics
    throw (Error.internal "solver failed to answer check-sat command")

  | some true =>
    -- cvc5 found a solution, we must retrieve the values we need
    let mut inputs := SymbolMap.empty
    -- using `getValues` instead of individual `getValue`-s to mix things up
    let vals ← getValues #[n1, n2, n3, flag, f]
    inputs := inputs.insert "n1" vals[0]!
    inputs := inputs.insert "n2" vals[1]!
    inputs := inputs.insert "n3" vals[2]!
    inputs := inputs.insert "flag" vals[3]!
    let fVal ← getValue f
    return (fVal, inputs)

  | some false =>
    -- cvc5 proved there is no `vals` such that `c (f vals)` is true
    return none

def adHocMinimize (c : Term → SmtM Term) : IO Unit := do
  let work := adHocMinimizeSmt c
  let res? ← work.runIO!
  match res? with
  | none => println! "no solution exists"
  | some (fVal, inputs) =>
    println! "found a solution with `f ... = {fVal}` for"
    for (var, val) in inputs do
      println! "- {var} := {val}"

/-- info: found a solution with `f ... = (- 11)` for
- flag := true
- n1 := (- 4)
- n2 := (- 4)
- n3 := (- 5)
-/
#guard_msgs in
#eval adHocMinimize (fun f => smt! f < (-10))

/-- info: found a solution with `f ... = (- 31)` for
- flag := true
- n1 := (- 9)
- n2 := (- 4)
- n3 := (- 5)
-/
#guard_msgs in
#eval adHocMinimize (fun f => smt! f < (-30))

/-- info: no solution exists -/
#guard_msgs in
#eval adHocMinimize (fun f => smt! f < (-1000000))

/-- info: found a solution with `f ... = (- 11)` for
- flag := true
- n1 := (- 4)
- n2 := (- 4)
- n3 := (- 5)
-/
#guard_msgs in
#eval adHocMinimize (smtFun! f => f < (-10)) -- `smtFun!`

end adhoc2



/-!
There's still a lot of room to mess up, for instance we will crash at runtime on

- ill-typed terms, which can happen in the `c` provided or in our code;
- `getValue` when not in *sat-mode*.

`cvc.lean` provides a safe(r) API by **strongly-typing** the notion of term and the commands that
can follow a `check-sat`.
-/
namespace adhocSafer

-- just add `.Safe` after `Cvc` to access the safe(r) API
open Cvc.Safe
open scoped Cvc.Safe.Term

/-- info: Cvc.Safe.Term (α : Type) : Type -/
#guard_msgs in
#check Term

/-- info: Cvc.Safe.Term.add {α : Type} [ArithLike α] (a b : Term α) : ManagerM (Term α) -/
#guard_msgs in
#check Term.add

/-- info: Cvc.Safe.Term.and (self that : Term Bool) : ManagerM (Term Bool) -/
#guard_msgs in
#check Term.and

open Smt in

def adHocMinimizeSmt
  -- already preventing bugs for users of this function
  (c : Term Int → SmtM (Term Bool))
: SmtM (Option Int) := do
  setOption .produceModels
  setLogic .qf_lia

  let n1 ← declareFun "n1" Int
  let n2 ← declareFun "n2" Int
  let n3 ← declareFun "n3" Int
  let flag ← declareFun "flag" Bool
  -- -- still works with functions too!
  -- let unknownFunction ← declareFun "unknownFunction" (Int → Bool → Int)

  -- using a term factory is tedious, so `cvc.lean` has syntax extensions to write terms in a
  -- (lean-)idiomatic fashion
  let constraints ← smt!
    (-10) ≤ n1 ∧ n1 ≤ 10 ∧
    (-10) ≤ n2 ∧ n2 ≤ 10 ∧
    (- 5) ≤ n3 ∧ n3 ≤  5 ∧
    (0 ≤ n2 → flag)
    -- -- still works with functions with lean-like syntax for application!
    -- ∧ unknownFunction n3 flag ≤ 7
  assert constraints

  -- `f`'s definition is nice and readable now
  let f ←
    smt! n1 - 2 * n2 + (if flag then (3 * (n3 + n1 - n2)) else (4 * (n1 - n3)))

  assert (← c f)

  checkSat
    (ifSat := do
      let _n1Val ← getValue n1
      let _n2Val ← getValue n2
      let _n3Val ← getValue n3
      let _flagVal ← getValue flag
      -- can't do anything with that currently...
      let fVal ← getValue f
      return some fVal)
    (ifUnsat := return none)
    (ifUnknown := panic! "omg!")

def adHocMinimize (c : Term Int → SmtM (Term Bool)) : IO Unit := do
  let work := adHocMinimizeSmt c
  let res? ← work.runIO!
  match res? with
  | none =>
    println! "no solution exists"
  | some fVal =>
    println! "found a solution with `f ... = {fVal}`"

/-- info: found a solution with `f ... = -11` -/
#guard_msgs in
#eval adHocMinimize (fun f => smt! f < (-10))

/-- info: found a solution with `f ... = -31` -/
#guard_msgs in
#eval adHocMinimize (fun f => smt! f < (-30))

/-- info: no solution exists -/
#guard_msgs in
#eval adHocMinimize (fun f => smt! f < (-1000000))

-- alternatively, with `smtFun!`/`smtPred`

/-- info: found a solution with `f ... = -11` -/
#guard_msgs in
#eval adHocMinimize (smtFun! f => f < (-10))

/-- info: found a solution with `f ... = -11` -/
#guard_msgs in
#eval adHocMinimize (smtPred! f => f < (-10))

end adhocSafer



/-! ## Let's make this more interesting -/

namespace betterSafer

/-!
How about we just let whoever is calling us specify the (strongly-typed) symbols they are interested in?

Ideally, users would write something like
-/

structure MySymbols.Lazy where
  n1 : Int
  n2 : Int
  n3 : Int
  flag : Bool

/-!
How close to this can `cvc.lean` get?
-/

open Cvc.Safe -- Safe(r) `Term`/`Smt`/... API
open scoped Cvc.Safe.Term -- `smt!` extension
open scoped Cvc.Safe.Symbols -- allows the notation below

/-- Putting `symbol` in front of structure is all you need. -/
symbol structure MySymbols where
  n1 : Int
  n2 : Int
  n3 : Int
  /-- Boolean flag. -/
  flag : Bool

/-- info: Demo.betterSafer.MySymbols.Idents : Type -/
#guard_msgs in
#check MySymbols.Idents

/-- info: Demo.betterSafer.MySymbols.Terms : Type -/
#guard_msgs in
#check MySymbols.Terms

/-- info: Demo.betterSafer.MySymbols.Values : Type -/
#guard_msgs in
#check MySymbols.Values

/-- info: Demo.betterSafer.MySymbols.idents : MySymbols.Idents -/
#guard_msgs in
#check MySymbols.idents

/-- info: |n1| -/
#guard_msgs in
#eval MySymbols.idents.n1

def f : MySymbols.Fun Int :=
  fun vars =>
    smt! vars.n1! - 2 * vars.n2! +
      if vars.flag!
      then (3 * (vars.n3! + vars.n1! - vars.n2!))
      else (4 * (vars.n1! - vars.n3!))

def domain : MySymbols.Pred :=
  smtFun! vars =>
    (-10) ≤ vars.n1! ∧ vars.n1! ≤ 10
    ∧ (-10) ≤ vars.n2! ∧ vars.n2! ≤ 10
    ∧ (- 5) ≤ vars.n3! ∧ vars.n3! ≤ 5
    ∧ (0 ≤ vars.n2! → vars.flag!)

/-!
Most features come from the `Cvc.Safe.Symbols` type-class, which acts as a specification for any
`symbol structure`.
The syntax extension does all the heavy-lifting, but instantiating `Symbols` yourself is not very
hard.

It's a bit of a complex type-class, let me just show you what using it looks like.
-/

/-- `R` is any `symbol structure`, *i.e.* a representation for some symbols. -/
structure Minimizer (Spec : Symbols R) where
  inputTerms : Spec.Terms
  f : Term Int

namespace Minimizer

variable [Spec : Symbols R]

open Smt

def init
  (logic : Logic)
  (f : Spec.Fun Int)
  (domain : Spec.Predicate)
: SmtM (Minimizer Spec) := do
  let inputIdents := Spec.idents

  setOption .produceModels
  setLogic logic
  let inputTerms ← inputIdents.declare
  let fTerm ← f inputTerms

  assert (← domain inputTerms)

  return ⟨inputTerms, fTerm⟩

variable (self : Minimizer Spec)

def check
  (self : Minimizer Spec)
  (assuming : Array (Term Bool) := #[])
: SmtM (Option (Int × Spec.Values)) := do
  checkSat assuming
    (ifSat := return some (← getValue self.f, ← self.inputTerms.getValues))
    (ifUnsat := return none)

def minimize (maxSteps : Nat) : SmtM (Option (Bool × Int × Spec.Values)) := do
  let some (fVal, inputs) ← self.check #[]
    | return none
  let mut fVal := fVal
  let mut inputs := inputs
  for _ in [0 : maxSteps] do
    let fValTerm ← Term.mkInt fVal
    let condition ← smt! self.f < fValTerm
    let some (fVal', inputs') ← self.check #[condition]
      | return (true, fVal, inputs) -- unsat: done, cannot be less than `fVal`
    -- otherwise, update and loop
    fVal := fVal'
    inputs := inputs'
  return (false, fVal, inputs)

end Minimizer

def minimize! [Spec : Symbols R]
  (logic : Logic)
  (f : Spec.Fun Int)
  (domain : Spec.Predicate)
  (maxSteps : Nat := 50)
: IO (Option (Bool × Int × Spec.Values)) :=
  let work := do
    let minimizer ← Minimizer.init logic f domain
    minimizer.minimize maxSteps
  work.runIO!

/-- info:
minimizing...
found a minimum :)
- f -10 10 -5 true := -105
-/
#guard_msgs in
#eval do
  println! "minimizing..."
  let maxSteps := 100
  match ← minimize! .qf_lia f domain maxSteps with
  | none => println! "no minimum found, domain is empty :/"
  | some (isMin, fVal, inputs) =>
    if isMin then
      println! "found a minimum :)"
    else
      println! "could not find a minimum in less than {maxSteps} steps :/"
      println! "here is the best I got"
    println! "- f {inputs.n1!} {inputs.n2!} {inputs.n3!} {inputs.flag!} := {fVal}"


namespace betterSafer
