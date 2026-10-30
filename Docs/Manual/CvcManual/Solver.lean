/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc
public meta import Cvc

import all cvc5
import all Cvc.Untyped.Core.Solver
import all Cvc.Typed.Core.Solver

public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External



set_option pp.rawOnError true



#doc (Manual) "Solver" =>
%%%
tag := "solver"
htmlSplit := .never
%%%

Similar to terms, solvers come in typed and untyped flavors, though they do not differ by much. The main differences are
- typed `Solver.assert` requires a `Term Bool`, instead of a `Term` for the untyped version, and
- typed model/value-retrieval as we will see below.

The rest of this section discusses typed solvers.

Solvers are tied to cvc5's notion of term manager, which means they are manager-scoped with a {lean}`Cvc.Ω` instance just like sorts and terms.

```lean -show
section typed
```

```lean
open Cvc Typed
variable [Ω]
```

# Basics

{docstring Cvc.Typed.Solver}

Solver creation and virtually all solver functions run in the {lean}`Env` monad.{margin}[Some run in stronger monads than {lean}`Env`, as we will see very soon.]

{docstring Cvc.Typed.Solver.new}

Some functions such as `setLogic` are actually defined on `Untyped.Solver`, but since `Typed.Solver` is just an alias for the untyped version we can use them on both types.

{docstring Cvc.Untyped.Solver.setLogic}
{docstring Cvc.Untyped.Solver.setOption}

Setting options also has a typed version that takes a {lean}`Solver.Option`, an enumeration of most of cvc5's options, and a value of the appropriate type for that option.

{docstring Cvc.Untyped.Solver.setOpt}

```lean
#eval Env.runIO do
  let solver ← Solver.new
  solver.setLogic .qf_lia
  solver.setOption "produce-models" "true"
  solver.setOpt .smt_produceUnsatCores true
  println! "logic: {← solver.getLogic}"
  let val ← solver.getOption "produce-models"
  println! "produce-models: {val}"
```

While it is possible to declare function symbols in a solver, it is strictly equivalent to creating a solver-agnostic symbol with `Term.mkSymbol`/`Term.mkSymbolAs`. Both simply create a new symbol in the underlying term manager.

```lean (name := ex_Solver_symbols)
#eval Env.runIO do
  let b ← Term.mkSymbol "b"
  let solver ← Solver.new
  let i ← solver.declareConst "i"
  let f ← Term.mkSymbolAs (Bool → Int → Int) "f"
  let g ← solver.declareFunAs (Int → Int → Int) "g"

  let t ← smt! 0 ≤ g (f b i) i
  solver.assert t
  solver.assert b
  println! "assertions:"
  for a in ← solver.getAssertions do
    -- note that `a : Term Bool`
    println! "- {a}"
```
```leanOutput ex_Solver_symbols
assertions:
- (<= 0 (g (f b i) i))
- b
```

As shown above `Solver.assert` adds a {lean}`Term Bool` assertion in the solver.

{docstring Cvc.Typed.Solver.assert}

# Check-sat and modal environments

The _check-sat_ function is significantly more complex, to see why let us look a the _get-value_ function first.

{docstring Cvc.Typed.Solver.getValue}

Since retrieving the value of a term is only legal (directly) after a check-sat that returned _sat_, cvc.lean strongly-types this fact with a _modal environment_, *i.e.* a monad specific to a solver being in _sat-mode_.

{docstring Cvc.Typed.Solver.EnvSat}

Cvc.lean has three of these, the other two being _unknown-mode_{margin}[Usually triggered by a timeout or when in an undecidable theory.] and _unsat-mode_.

{docstring Cvc.Typed.Solver.getUnsatCore}
{docstring Cvc.Typed.Solver.EnvUnsat}

{docstring Cvc.Typed.Solver.getTimeoutCore}
{docstring Cvc.Typed.Solver.EnvUnknown}

To guarantee modal code is safe to run, cvc.lean does not allow users to directly run it: it must be passed alongside a check-sat query to guarantee that only the appropriate sat/unsat/unknown code runs. Hence the signature of the solver check-sat function:

{docstring Cvc.Typed.Solver.checkSat}

The only argument left to explain is `assuming` which is an optional array of {lean}`Term Bool` providing additional assumptions for this check-sat, called `check-sat-assuming` in SMT-LIB 2.7.

```lean (name := ex_Solver_modal1)
#eval Env.runIO do
  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  solver.setOpt .smt_produceUnsatCores true
  let b ← Term.mkSymbol "b"
  let i1 ← Term.mkSymbol "i1"
  let i2 ← Term.mkSymbol "i2"
  let not_b ← smt! ¬ b
  smt! i2 = 7 >>= solver.assert
  smt! 0 ≤ i1 >>= solver.assert
  smt! b ∨ i1 < 0 >>= solver.assert

  let core ← solver.checkSat (assuming := #[not_b])
    (ifUnsat := solver.getUnsatCore)
  println! "unsat core, not necessarily minimal:"
  for t in core do println! "- {t}"

  -- `Solver.getValue` extracts lean values
  let (bVal, i1Val, i2Val) ← solver.checkSat
    (ifSat := return (
      ← solver.getValue b,
      -- there's also a `getValue` function on terms
      ← i1.getValue,
      ← solver.getValue i2))
  println! "model as Lean values:\n\
    - b  := {bVal}\n- i1 := {i1Val}\n- i2 := {i2Val}"

  -- `Solver.getValueTerm` extracts (typed) cvc terms
  let (bVal, i1Val, i2Val) ← solver.checkSat
    (ifSat := return (
      ← solver.getValueTerm b,
      -- there's also a `getValueTerm` function on terms
      ← i1.getValueTerm,
      ← solver.getValueTerm i2))
  println! "model as cvc terms:\n\
    - b  := {bVal}\n- i1 := {i1Val}\n- i2 := {i2Val}"

  -- we can always erase type information if needed
  let vals ← solver.checkSat
    (ifSat := do
      let bVal ← solver.getValueTerm b
      let i1Val ← solver.getValueTerm i1
      let i2Val ← solver.getValueTerm i2
      return #[ bVal.erase, i1Val.erase, i2Val.erase ])
  println! "untyped model: {vals}"
```
```leanOutput ex_Solver_modal1
unsat core, not necessarily minimal:
- (not b)
- (= i2 7)
- (<= 0 i1)
- (or b (< i1 0))
model as Lean values:
- b  := true
- i1 := 0
- i2 := 7
model as cvc terms:
- b  := true
- i1 := 0
- i2 := 7
untyped model: #[true, 0, 7]
```

# More check-sat functions

For simple check-sat use cases where the only thing that matters is whether the current assertions are satisfiable or not one can simply use {lean}`Solver.checkIsSat`.

{docstring Cvc.Typed.Solver.checkIsSat}

Oftentimes we want to return a result specific to a sat/unsat result, and nothing otherwise, for instance a model on a sat result and nothing on unsat. In such cases it can be easier to use `Solver.checkSat?` which lets the caller specify which outcome produces a result and how, the unexpected result producing {lean}`none` by default.{margin}[On an _unknown_ outcome, the default throws an error instead of returning {lean}`none` as _unknown_ is considered to never be expected by default.]

{docstring Cvc.Typed.Solver.checkSat?}

```lean (name := ex_Solver_moreCheckSat)
#eval Env.runIO do
  let b ← Term.mkSymbol "b"
  let i1 ← Term.mkSymbol "i1"
  let i2 ← Term.mkSymbol "i2"
  let t1 ← smt! b ∧ 0 < i1
  let t2 ← smt! i1 % i2 = i1
  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  if ← solver.checkIsSat then
    println! "sat, adding constraint"
    let values? ← solver.checkSat? (assuming := #[t2])
      (ifSat := return some (← i1.getValue, ← i2.getValue))
    if let some (i1Val, i2Val) := values?
    then println! "  i1 := {i1Val}, i2 := {i2Val}"
    else println! "  unsat with additional constraints"
  else println! "unsat"
```
```leanOutput ex_Solver_moreCheckSat
sat, adding constraint
  i1 := 0, i2 := 0
```

# Defining (recursive) function symbols

> Unlike declaring a function symbol, _defining_ one is a solver-specific action as it implies a solver-level constraint to tie the symbol and its definition together.

Defining a function symbol in a solver is very similar to building a lambda: the resulting term must be typed from its bound variables.

{docstring Cvc.Typed.Solver.defineFun}

```lean (name := ex_Term_bVars_defineFun)
#eval Env.runIO do
  let ub ← Term.mkSymbolAs Int "upperBound"
  let solver ← Solver.new
  solver.setOpt .smt_produceModels true

  let (i, j) := (← Term.mkBVar "i", ← Term.mkBVar "j")
  let bVars := BVars.empty.push i |>.push j
  let saturatingMaxDef ← (smt!
    let max ← if j ≤ i then i else j;
    if max < ub then max else ub)
  println! "saturatingMaxDef := {saturatingMaxDef}"

  let sMax ← solver.defineFun
    "saturatingMax" bVars saturatingMaxDef
  smt! sMax 17 21 < ub >>= solver.assert
  solver.checkSat (ifSat := do
    println! "ub := {← ub.getValue}")
```
```leanOutput ex_Term_bVars_defineFun
saturatingMaxDef := (let ((_let_1 (ite (<= j i) i j))) (ite (< _let_1 upperBound) _let_1 upperBound))
ub := 22
```

## Mutually recursive function symbols

Cvc.lean does not, currently, expose special functions for defining mutually recursive functions in its typed API. The untyped API does, which is what we present below.

```lean -show
end typed

section untyped
```

```lean
open Cvc Untyped
variable [Ω]
```

```lean (name := ex_Term_defFunsRec)
#eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  solver.setOption "fmf-fun" "true"
  let even ← solver.declareFun "even" #[int] bool
  let odd ← solver.declareFun "odd" #[int] bool
  let n ← Term.mkBVar int "n"
  let m ← Term.mkBVar int "m"
  solver.defineFunsRec #[even, odd] #[#[n], #[m]] #[
    ← smt! if n ≤ 0 then n = 0 else odd (n - 1),
    ← smt! if m ≤ 0 then false else even (m - 1)]
  let i ← Term.mkSymbol int "i"
  smt! 3 ≤ i >>= solver.assert
  println! "forcing even"
  solver.checkSat (assuming := #[← smt! even i])
    (ifSat := do println! "  sat, i := {← i.getValue}")
  println! "forcing odd"
  solver.checkSat (assuming := #[← smt! odd i])
    (ifSat := do println! "  sat, i := {← i.getValue}")
```
```leanOutput ex_Term_defFunsRec
forcing even
  sat, i := 4
forcing odd
  sat, i := 3
```
