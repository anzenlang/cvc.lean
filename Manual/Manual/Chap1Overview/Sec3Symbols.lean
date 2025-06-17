/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import VersoManual

import Manual.Meta.Lean

import Cvc

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Manual

open Cvc

set_option pp.rawOnError true


#doc (Manual) "Symbols, States and Systems" =>

%%%
tag := "chapOverview_symbols"
%%%

> *NB*: this section is not just an overview of a specific part of cvc.lean. It also serves as an
> example of the kind of very, very specialized API that can be built on top of this library thanks
> to Lean 4's extreme flexibility; and cvc.lean's design itself, also.

Ergonomics is such a big concern for cvc.lean that it goes way beyond being a strongly-typed-lean
version of the original cvc5 `C++` API. I also provides very high-level features for typical SMT
solver use cases.

This is a necessity to some extent: strongly-typed terms mean that in general we cannot put all our
terms in a collection (typically a red/black map from names to terms): some may be {lean}`Term Bool`
while others are {lean}`Term Int`, or anything else, or the actual type the terms may not even be
known at compile-time.

For instance, say we're solving some linear constraints over three variables/symbols `x`, `y`, and
`z`. We could follow the same workflow as the previous examples and handle each variable separately.
That would be pretty cumbersome, not to mention tedious if we have many variables and keep passing
them around to functions that create terms/do SMT-things using these variables.

We could just define our own structure, something like this:

```lean
structure AdHocVars where
  flag : Term Bool
  x : Term Int
  y : Term Int
  z : Term Int
```

We still need to declare variables one-by-one and build the structure, but at least we can pass
terms for the variables more efficiently. Assuming we want to retrieve {lean}`Value`s for these
variables at some point, we now need to either retrieve the values one-by-one, or define and
instrument a special structure for that.

```lean
namespace AdHocVars
def declare : Smt AdHocVars := do
  let flag ← Smt.declare "flag" Bool
  let x ← Smt.declare "x" Int
  let y ← Smt.declare "y" Int
  let z ← Smt.declare "z" Int
  return ⟨flag, x, y, z⟩

structure Values where
  flag : Value Bool
  x : Value Int
  y : Value Int
  z : Value Int

def getModel (vars : AdHocVars) : Smt.Sat Values := do
  let flag ← Smt.getValue vars.flag
  let x ← Smt.getValue vars.x
  let y ← Smt.getValue vars.y
  let z ← Smt.getValue vars.z
  return ⟨flag, x, y, z⟩
end AdHocVars
```

This is fine, but clearly one could provide a more generic way to define a symbol structure and jump
between symbols, terms, values, and more.

The {lean}`Symbols` class does exactly that. We will not discuss it in details in this overview
and instead just showcase what it lets us do. It comes with a syntax extension for defining symbol
structures that we use right away.

```lean
open Cvc.Symbols.Dsl

/-- My variables. -/
symbol structure Vars where
  /-- Some Boolean flag. -/
  flag : Bool
  /-- My first variable. -/
  x : Int
  /-- My second variable. -/
  y : Int
  /-- My last variable. -/
  z : Int
```

This defines a {lean}`Vars` structure:

```savedLean (name := symbolsDemo1)
#print Vars
```

```leanOutput symbolsDemo1
structure Vars (R : Symbol.Repr) : Type
number of parameters: 1
fields:
  Vars.flag : R Bool
  Vars.x : R Int
  Vars.y : R Int
  Vars.z : R Int
constructor:
  Vars.mk {R : Symbol.Repr} (flag : R Bool) (x y z : R Int) : Vars R
```

Without getting too technical, this makes {lean}`Vars` flexible regarding type of its fields. Of
particular interest are

- {lean}`Vars.Idents`: fields are just their name, for instance `flag := "flag"`.

  Pre-declaration version of {lean}`Vars`, already built for us by {lean}`Vars.idents`.

  ```lean
  #print Vars.Idents
  #print Vars.idents
  ```

- {lean}`Vars.Terms`: fields are symbol-terms, for instance `flag : Term Bool`.

  ```lean
  #print Vars.Terms
  ```

  Result of declaring {lean}`Vars.Idents`, see example below.

- {lean}`Vars.Model`: fields are values, for instance `flag : Value Bool`.

  ```lean
  #print Vars.Model
  #print Vars.Values -- alias for `Vars.Model`
  ```

  Result of get-value-ing {lean}`Vars.Terms`, see example below.

- {lean}`Vars.Predicate`: a function taking a {lean}`Vars.Terms` and producing a {lean}`Formula` in
  the {lean}`Term.Build` monad.

  If you don't like long names, use its alias {lean}`Vars.Pred`.

  ```lean
  #print Vars.Predicate
  #print Vars.Pred
  ```

With {lean}`Vars` and know a little bit about its bells and whistles, instrumentation is easy.

```lean
namespace Vars

open Cvc.Term.Dsl

def solveIO
  (constraints : Array Vars.Predicate)
: IO (Option Vars.Model) := Smt.runIO do
  -- don't forget this (I always do)
  Smt.setOption .produceModels

  -- `Vars` already knows its own identifiers
  let idents := Vars.idents
  -- declaration is straightforward
  let vars ← idents.declare

  for constraint in constraints do
    Smt.assert (← constraint vars)

  Smt.checkSatAnd
    (ifSat := do
      -- retrieving the model is easy:
      let model ← vars.getModel
      return some model)
    (ifUnsat := return none)

def solveShowIO
  (constraints : Array Vars.Predicate)
: IO Unit := do
  if let some model ← solveIO constraints then
    println! "found a solution 😺"
    -- the fields of `Vars` are more complex than presented
    -- above: they also carry the `.name` of the symbol
    println! "  \
      {model.flag.name} ↦ {model.flag}, \
      {model.x.name} ↦ {model.x}, \
      {model.y.name} ↦ {model.y}, \
      {model.z.name} ↦ {model.z}\
    "
  else println! "no solution exists 😿"

end Vars
```

Let's put it all together and solve some equations. We use the `smtPred!` part of the `Cvc.Term.Dsl`
which makes it easy to define a function into a {lean}`Term.Build Formula`. It is essentially the
same as `fun vars => smt! ...`.

```savedLean (name := symbolsDemo3)
open Cvc.Term.Dsl in
#eval Smt.runIO do
let constraints : Array Vars.Predicate := #[
  smtPred! vars => 2*vars.x + vars.y - 2 * vars.z = 3,
  smtPred! vars => vars.x - vars.y - vars.z = 0,
  -- implication is written `→` in `smt!`
  smtPred! ⟨flag, x, y, z⟩ => flag → x + y + 3 * z = 12,
  smtPred! ⟨flag, x, y, z⟩ => flag → x + y + z = 0,
]

println! "solving without forcing `flag`..."
Vars.solveShowIO constraints
println! "\nsolving with `flag` force to true..."
Vars.solveShowIO <| constraints.push (smtPred! vars => vars.flag)
```

```leanOutput symbolsDemo3
solving without forcing `flag`...
found a solution 😺
  flag ↦ false, x ↦ 1, y ↦ 1, z ↦ 0

solving with `flag` force to true...
no solution exists 😿
```

That's already pretty good, but we're just getting started. A common use case for SMT solvers is
_model-checking_ for _transition system_. A concrete example follows, but very briefly a transition
system is three things:

- a notion of _state_: a bunch of symbols/variables, such as our {lean}`Vars` symbol structure;
- some constraints `init` over a state specifying the initial states of the system;
- some constraints `step` _between two states_ `current` and `next` specifying that `next` is
  a _successor_ of `current`.

Given some notion of state, such systems can take various forms, for instance
[Constrained Horn Clauses][chc]. Let's keep things simple and just see them as an `init` _predicate_
over a state ≈ `State → Formula`, and a `step` _relation_ over two states ≈
`State → State → Formula`.

Take for instance a stopwatch system with two inputs: `startStop reset : Bool`, an output
`counting : Int` counting the time, and an internal variable `isCounting : Bool` keeping track of
whether the stopwatch is counting. Then, we could define this system as

```lean
namespace Implemented

structure State where
  startStop : Bool
  reset : Bool
  isCounting : Bool
  counting : Int

def init (state : State) : Bool :=
  ¬ state.isCounting ∧ state.counting = 0

def step (curr next : State) : Bool :=
  next.isCounting =
    if next.startStop then ¬ curr.isCounting
    else curr.isCounting
  ∧
  next.counting =
    if next.reset then 0
    else if next.isCounting then curr.counting + 1
    else curr.counting

end Implemented
```

Once we have such a representation, model-checking consists in checking whether some _properties_
(state-predicates) are verified by the system. That is, the properties are true in all _reachable
states_ (reachable through `step`-transition(s) from `init`) in which case each property is called
an _invariant_ of the system. If not, model-checkers are expected to produce a _counterexample_
(_cex_) trace: a sequence of concrete (valued) states such that
- the first one verifies `init`,
- element `i+1` is a `step`-successor of element `i`, and
- the last element makes a property false.

On {lean}`Implemented.State` for instance:

- `0 ≤ state.counter` is an invariant;

- `state.counter ≠ 2` is not an invariant.

  Writing states as `⟨startStop, reset, isCounting, counter⟩`, a cex trace for it could be

  - `⟨true, false, false, 0⟩` at `0` - initial state
  - `⟨true, false, true, 1⟩` at `1` - `step` holds between `0` and `1`
  - `⟨false, false, true, 2⟩` at `2` - `step` holds between `1` and `2`

Now, in this context we immediately run into the notion of _unrolling_. We're not just talking about
a notion of symbols in the sense of {lean}`Vars` from previous examples, we would ideally like to
talk about state symbols/terms/values that can be _unrolled_ at some index `k : Nat`.

In an ideal world, we could just use the symbol-structure from previous example and replace
`symbol structure ...` with `state structure ...`. Something like this:

```lean
open Cvc.State.Dsl in

/-- State structure. -/
state structure Sw.State where
  /-- Input start/stop button. -/
  startStop : Bool
  /-- Input reset button. -/
  reset : Bool
  /-- Internal is-counting flag. -/
  isCounting : Bool
  /-- Output time counter. -/
  counter : Int
```

_State-structures_ give us access to all the usual symbol goodies ({lean}`Sw.State.Idents`,
{lean}`Sw.State.Terms`, {lean}`Sw.State.Model`) but also to unrolling-specific versions:
{lean}`Sw.State.IdentsAt`, {lean}`Sw.State.TermsAt`, and {lean}`Sw.State.ModelAt`.

::::leanSection
```lean (show := false)
variable (k : Nat)
```

They also give access to {lean}`Sw.State.PredicateAt` ({lean}`Sw.State.PredAt`) and
{lean}`Sw.State.RelationAt` ({lean}`Sw.State.RelAt`). They let us express, respectively, state
predicates at some unrolling depth {lean}`Sw.State.PredicateAt k` and state relations between a
state at `k` and a state at `k + 1`: {lean}`Sw.State.RelationAt k`.

Because predicates/relations are strongly-typed on their unrolling depth, this prevents a lot of
errors where we would pass states at an incorrect depth to a relation-term-builder or a function
checking a predicate at a precise depth.
::::

We're still missing a notion of trace, and if we are being honest we just want a notion of system
that takes our `init`, `step`, and _candidates_ (properties) and just do everything for us.
Introducing the _system structure_ syntax extension, applied here to {lean}`Sw.State` defined above.

```lean
open Cvc.Term.Dsl
open Cvc.Sys.Dsl

/-- Stopwatch system. -/
system structure Sw for Sw.State where
  init : Sw.State.StatePred :=
    smtPred! state => ¬ state.isCounting ∧ state.counter = 0
  step : Sw.State.StateRel := smtRel! curr next =>
    (
      next.isCounting =
        if next.startStop then ¬ curr.isCounting
        else curr.isCounting
    ) ∧ (
      next.counter =
        if next.reset then 0 else
          if next.isCounting then curr.counter + 1
          else curr.counter
    )
  namedCandidates := .ofList [
    ("counter positive",
      smtPred! state => 0 ≤ state.counter),
    ("counter ≠ 2",
      smtPred! state => state.counter ≠ 2),
  ]
```

{lean}`Sw` is two things:
- a {lean}`Symbols.Unroller` that handles states ({lean}`Sw.State`) as well as our `init` predicate
  and `step` relation.
- some {lean}`Sys.Candidates` that keep track of each {lean}`Sys.Candidate`'s _status_.

::::leanSection

```lean (show := false)
variable (length : Nat)
```

Now, {lean}`Sw` is parameterized by a {lean}`Nat` which, crucially, does *not* correspond to the
unrolling depth. {lean}`Sw length` denotes *unrolled systems of {lean}`length` state(s)*, meaning
that {lean}`Sw 0` is an unrolling of `0` states. {lean}`Sw 1` is an unrolling of `1` state.
{margin}[
  This is a bit weird, but it allows creating a {lean}`Sw 0` without declaring any term, _i.e._
  without being in the {lean}`Smt` monad.
]

::::

Let's instrument {lean}`Sw` so that we can display what the candidate statuses are.

```lean
namespace Sw

/-- `Sw k.succ`, in `Sw 0` candidates have no status. -/
def print {k : Nat} (sw : Sw k.succ) : IO Unit := do
  println! "candidates status at depth {k}:"
  let .mk unknown invariant falsified := sw.candidates

  if ¬ unknown.isEmpty then
    println! "- {unknown.size} unknown(s)"
    for (name, unk) in unknown do
      let baseUpTo :=
        if let some k := unk.baseValidUpTo?
        then s!", valid up to step {k}"
        else ""
      println! "  `{name}`{baseUpTo}"

  if ¬ invariant.isEmpty then
    println! "- {invariant.size} invariant(s)"
    for (name, inv) in invariant do
      println! "  `{name}`, {inv.provedAt}-inductive"

  if ¬ falsified.isEmpty then
    println! "- {falsified.size} falsified"
    for (name, fls) in falsified do
      println! "  `{name}`, \
        falsified in {fls.falsifiedAt} steps"
      for ⟨k, state⟩ in fls.cex do
        println! "  - at {k}: \
          startStop := {state.startStop}, \
          reset := {state.reset}, \
          isCounting := {state.isCounting}, \
          counter := {state.counter}\
        "

end Sw
```

Feel free to dive into the {lean}`Cvc.Sys` API, but let's conclude our discussion of strongly-typed
symbols/states/systems the output of the _do-it-for-me_ function {lean}`Cvc.Sys.kInduction`.

First, let's only allow unrolling up to two states, meaning one `step`:

```savedLean (name := sysDemo1)
#eval Smt.runIO do
  Smt.setOption .produceModels
  -- none of the type annotations are needed
  let stateIdents := Sw.State.idents
  let sw0 : Sw 0 := Sw.ofIdents stateIdents
  let maxSteps := 2
  println! "running with `maxSteps := {maxSteps}`"
  let res : (k : Nat) × Sw k.succ ← sw0.kInduction maxSteps
  let ⟨k, sw⟩ := res
  println! "→ done at `length = {k.succ} = depth + 1`\n"
  sw.print
```

```leanOutput sysDemo1
running with `maxSteps := 2`
→ done at `length = 2 = depth + 1`

candidates status at depth 1:
- 1 unknown(s)
  `counter ≠ 2`, valid up to step 1
- 1 invariant(s)
  `counter positive`, 1-inductive
```

That was not enough to falsify our bad candidate. Let's start again but unroll deeper.

```savedLean (name := sysDemo2)
#eval Smt.runIO do
  Smt.setOption .produceModels
  -- none of the type annotations are needed
  let stateIdents : Sw.State.Idents := Sw.State.idents
  let sw0 : Sw 0 := Sw.ofIdents stateIdents
  let maxSteps := 10
  println! "running with `maxSteps := {maxSteps}`"
  let res : (k : Nat) × Sw (k + 1) ← sw0.kInduction maxSteps
  let ⟨k, sw⟩ := res
  println! "→ done at `length = {k.succ} = depth + 1`\n"
  sw.print
```

```leanOutput sysDemo2
running with `maxSteps := 10`
→ done at `length = 3 = depth + 1`

candidates status at depth 2:
- 1 invariant(s)
  `counter positive`, 1-inductive
- 1 falsified
  `counter ≠ 2`, falsified in 2 steps
  - at 2: startStop := false, reset := false, isCounting := true, counter := 2
  - at 1: startStop := true, reset := false, isCounting := true, counter := 1
  - at 0: startStop := false, reset := false, isCounting := false, counter := 0
```

Before moving on, note that {lean}`Sys.kInduction` is not limited to `Sw 0`. Let's see what
combining the two previous examples looks like before moving on.

```savedLean (name := sysDemo3)
#eval Smt.runIO do
  Smt.setOption .produceModels
  -- none of the type annotations are needed
  let stateIdents := Sw.State.idents
  let sw0 : Sw 0 := Sw.ofIdents stateIdents
  let maxSteps := 2
  println! "running with `maxSteps := {maxSteps}`"
  let res : (k : Nat) × Sw k.succ ← sw0.kInduction maxSteps
  let ⟨k, sw⟩ := res
  println! "→ done at `length = {k.succ} = depth + 1`\n"
  sw.print

  if sw.isDone then
    println! "\nunexpected: no more unknown candidates"
    return ()

  println! "\nsome candidates are still unknown...\n"
  let maxSteps := 10
  println! "running with `maxSteps := {maxSteps}`"
  let res : (k : Nat) × Sw (k + 1) ← sw.kInduction maxSteps
  let ⟨k, sw⟩ := res
  println! "→ done at `length = {k.succ} = depth + 1`\n"
  sw.print
```

```leanOutput sysDemo3
running with `maxSteps := 2`
→ done at `length = 2 = depth + 1`

candidates status at depth 1:
- 1 unknown(s)
  `counter ≠ 2`, valid up to step 1
- 1 invariant(s)
  `counter positive`, 1-inductive

some candidates are still unknown...

running with `maxSteps := 10`
→ done at `length = 3 = depth + 1`

candidates status at depth 2:
- 1 invariant(s)
  `counter positive`, 1-inductive
- 1 falsified
  `counter ≠ 2`, falsified in 2 steps
  - at 2: startStop := false, reset := false, isCounting := true, counter := 2
  - at 1: startStop := true, reset := false, isCounting := true, counter := 1
  - at 0: startStop := false, reset := false, isCounting := false, counter := 0
```


[smtlib]: https://smt-lib.org
[chc]: https://en.wikipedia.org/wiki/Constrained_Horn_clauses
