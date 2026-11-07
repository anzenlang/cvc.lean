/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Basic
public import Cvc.Logic
public import Cvc.Defs
public import Cvc.Srt
public import Cvc.Types
public import Cvc.Spec
public import Cvc.Gen
public import Cvc.Ext
public import Cvc.Untyped
public import Cvc.Typed



namespace Cvc

/-! # A high-level, safety-oriented API for cvc5

This library drives the [cvc5](https://cvc5.github.io) SMT solver from Lean. It sits on top of
[lean-cvc5](https://github.com/abdoo8080/lean-cvc5), a thin binding over cvc5's C++ API, and turns
the mistakes that binding reports at runtime, or does not report at all, into errors Lean reports at
compile time.

The [user manual](https://www.anzenlang.io/cvc.lean/manual/) explains the library in detail, and
its [overview](https://www.anzenlang.io/cvc.lean/manual/Overview/) shows the main features on
examples.

## Environments, `Ω`, and running them

Everything cvc5 creates — sorts, terms, solvers — belongs to a *term manager*, and objects of two
different managers must never meet. This library never shows you a term manager. In its place is the
class `Ω`, whose instances stand for "the term manager of the current scope". Nearly every type and
function takes one implicitly, and two values can only meet when they share one.

Work happens in the **environment monad** `Env`. An `Env α` builds and manipulates terms, drives
solvers, and can throw a `Cvc.Error`; it also lifts `IO`, so `println!` works inside it. `EnvT m` is
the transformer, for a base monad other than `BaseIO`.

**You cannot make an `Ω` yourself**: running an environment is the only place one comes from.

```lean
Env.run   : ([Ω] → Env α) → BaseIO (Res α)   -- errors as a value
Env.runIO : ([Ω] → Env α) → IO α             -- errors as an `IO` exception
EnvT.run  : ([Ω] → EnvT m α) → m (Res α)
```

Each run creates a fresh term manager, hands your code an `Ω` standing for it, and is the whole
lifetime of that manager. Since `α` is chosen outside the run, a `Term`, an `Srt` or a `Solver`
cannot escape it, while a Lean value read out of a model can.

A definition mentioning `Env`, `Term`, `Srt` or `Solver` should take an `Ω` instance, most easily
through `variable [Ω]`: it then works in whichever scope calls it, and `Env.run` is called once, at
the edge. Without one, it fails to compile with `failed to synthesize Ω`.

## Two layers

Terms come in two flavours, which share the environment, the solver and the sorts.

- **`Cvc.Untyped`**: a `Term` carries no Lean-side sort. It is close to cvc5 itself, and a sort
  mistake is cvc5's to report, at runtime.
- **`Cvc.Typed`**: a `Term α` is indexed by the Lean type its sort denotes — `Term Int`,
  `Term (Set Bool)`, `Term (Int → Bool)`. A sort mistake is a Lean type error, and a model value
  comes back as an `Int`, a `Set Bool`, with nothing to convert.

`Typed.Term.erase` goes down for free, and `Untyped.Term.typeCheck` goes up by checking the term's
sort. `open Cvc.Untyped` or `open Cvc.Typed` selects a layer, along with its spelling of the `smt!`
notation, which writes terms in something close to Lean's own syntax: `smt! i + 2 * j ≤ k ∧ ¬ b`.

## Solving

A `Solver` is created inside an environment with `Solver.new`, and is fed assertions with
`Solver.assert`. `Solver.checkSat` takes one branch per possible answer, and each branch runs in a
monad that only allows what that answer makes meaningful: reading a model is only possible in the
`ifSat` branch, an unsat core only in `ifUnsat`. Those monads are indexed by the solver that
answered, so one solver's model cannot be read through another.

## What to import

This root module imports everything. Importing only the layer you use (`Cvc.Typed`, `Cvc.Untyped`)
or only the theories you need (`Cvc.Typed.Theory.Arith`, …) compiles less, and `smt!` then accepts
only the notations of the theories imported.
-/
