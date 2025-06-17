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


#doc (Manual) "Solver" =>

%%%
tag := "chapOverview_solver"
%%%

Building terms is fun but it's not much use unless we use them in a solver. Like term creation,
solver interaction happens in an error/state monad: {lean}`Smt`.
{margin}[
  For the monad *transformer* version, see {lean}`SmtT`.
]
Its API is based on the usual [SMT-LIB][smtlib] commands, for instance:

{docstring Smt.declare}

{docstring Smt.assert}

Cvc.lean's version of `check-sat` includes the `check-sat-assuming` variant.
{margin}[
  As a reminder, `check-sat-assuming` allows to check the current assertions while assuming, _just
  for the current check_, that some `Bool` literals are true.
]
It's actually more powerful in that it allows to assume any {lean}`Term Bool`, not just `Bool`
literals.

{docstring Smt.checkSat}

We will use a different `check-sat` version in the following, as the results it returns are easier
to deal with.

{docstring Smt.checkSat?}

These basic SMT functions are enough to `checkSat` some constraints. Note that {lean}`Smt` also
allows term-building.

```savedLean (name := smtDemo1)
open Cvc.Term.Dsl in
open Smt in
#eval Cvc.Smt.runIO do
  let x ← declare "x" Int
  let y ← declare "y" Int
  let eq1 ← smt! 2 * x + y = 5
  println! "asserting {eq1}"
  assert eq1

  let eq2 ← smt! (-x) + y = 2
  println! "asserting {eq2}"
  assert eq2

  println! "check-sat-ing:"
  match ← checkSat? with
  | none => println! "→ unknown"
  | some true => println! "→ sat"
  | some false => println! "→ unsat"
```

```leanOutput smtDemo1
asserting (= (+ (* 2 x) y) 5)
asserting (= (+ (- x) y) 2)
check-sat-ing:
→ sat
```

Nice, but how about retrieving the satisfying assignment for `x` and `y`, _i.e._ the _model_? Sure
enough, there is a `get-value`-like function in the {lean}`Smt` namespace:

{docstring Smt.getValue}

Let's first note that this function does not return a term but a {lean}`Value` instead. This is just
a wrapper around a term but specifies that the term was created by retrieving the value of another
term. This means that, if the logics/assertions are simple enough, a {lean}`Value` is often a
constant {lean}`Term` such as a Boolean/integer constant.

Moving on, it might be surprising that this function is *not* in the {lean}`Smt` monad, but instead
in {lean}`Smt.Sat`. This is because getting the value of a symbol such as `x` is only valid right
after a `check-sat` that confirmed the assertions are satisfiable. {lean}`Smt.Sat` is the monad
corresponding to this exact context.
{margin}[
  See also {lean}`Smt.Unsat`/{lean}`Smt.Unknown` for the unsat/unknown equivalent.
]

{docstring Smt.Sat}

The only way to run code in this monad is through yet another `check-sat` variant:

{docstring Smt.checkSatAnd}

Its signature is a bit daunting, though we have already discussed the `assuming` part. All it does
is perform a `check-sat` and immediately run one of the three `if<result>` continuations depending
on the outcome of the check. Their default values are there for convenience and fail by saying that
the corresponding outcome was not expected.

Let's now retrieve the model for `x` and `y` in the previous example. In order two do so we must
activate model production using {lean}`Smt.setOption` with the appropriate {lean}`Cvc.Option`.

```savedLean (name := smtDemo1)
open Cvc.Term.Dsl in
open Smt in
#eval Cvc.Smt.runIO do
  setOption .produceModels
  let x ← declare "x" Int
  let y ← declare "y" Int
  let eq1 ← smt! 2 * x + y = 5
  println! "asserting {eq1}"
  assert eq1

  let eq2 ← smt! (-x) + y = 2
  println! "asserting {eq2}"
  assert eq2

  println! "check-sat-ing:"
  checkSatAnd
    (ifUnsat := println! "→ unsat 🙀")
    (ifSat := do
      println! "→ sat:"
      let xValue ← getValue x
      println! "  x := {xValue}"
      let yValue ← getValue y
      println! "  y := {yValue}"

      -- we can also build terms in here
      let eq1Lhs ← getValue (← smt! 2 * x + y)
      let eq2Lhs ← getValue (← smt! (-x) + y)
      println! "  eq1Lhs: {eq1Lhs}"
      println! "  eq2Lhs: {eq2Lhs}")
    -- no `ifUnknown` continuation provided
```

```leanOutput smtDemo1
asserting (= (+ (* 2 x) y) 5)
asserting (= (+ (- x) y) 2)
check-sat-ing:
→ sat:
  x := 1
  y := 3
  eq1Lhs: 5
  eq2Lhs: 2
```

[smtlib]: https://smt-lib.org
