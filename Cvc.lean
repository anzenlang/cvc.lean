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

ping

This library drives the [cvc5](https://cvc5.github.io) SMT solver from Lean. It sits on top of
[lean-cvc5](https://github.com/abdoo8080/lean-cvc5), a thin binding over cvc5's C++ API, and its
purpose is to turn the mistakes that binding reports at runtime — or does not report at all — into
errors Lean reports at compile time.

## Environments, `Ω`, and running them

Everything cvc5 creates — sorts, terms, solvers — belongs to a *term manager*, and objects of two
different managers must never meet. This library never shows you a term manager. In its place is the
class `Ω`, a proposition whose instances stand for "the term manager of the current scope". Nearly
every type and function takes one implicitly: `Term α`, `Srt` and `Solver` all mean "of the scope's
manager", and two of them can only meet when they share one.

Work happens in the **environment monad** `Env`, itself (implicitly) parameterized by `Ω`. An `Env
α` (or `@Env Ω α`) builds and manipulates terms, drives solvers, and can throw a `Cvc.Error`; it
also lifts `IO`, so `println!` works inside it. `EnvT m` is the transformer, for a base monad other
than `BaseIO`.

**You cannot make an `Ω` yourself.** Its constructor is private, and the only place one comes from
is running an environment:

```lean
Env.run   : ([Ω] → Env α) → BaseIO (Res α)   -- errors as a value
Env.runIO : ([Ω] → Env α) → IO α             -- errors as an `IO` exception
EnvT.run  : ([Ω] → EnvT m α) → m (Res α)
```

Each run creates a fresh term manager, hands your code an `Ω` standing for it, and is the whole
lifetime of that manager. The `[Ω] →` in the argument is the point: `α` is chosen *outside*, where
no `Ω` exists, so it cannot mention one. A `Term`, an `Srt` or a `Solver` therefore cannot escape a
run — `Env.runIO (Term.mkInt 3) : IO (Term Int)` does not typecheck — while a Lean value read out of
a model can. This is the `runST` discipline, applied to term managers.

### Always write `Env` code with an `Ω` in scope

The consequence for writing code is simple and worth following without exception: **every definition
that mentions `Env`, `Term`, `Srt` or `Solver` takes an `Ω` instance**, most easily by opening a
section with `variable [Ω]`. Such a definition does not pick a scope; it works in *whichever* scope
calls it, and `Env.run` is called once, at the edge, to supply one.

```lean
open Cvc Typed

section variable [Ω]

/-- `x + x`, in whatever scope calls it. -/
def double (x : Term Int) : Env (Term Int) := smt! x + x

/-- Finds an `x` such that `double x = 6`. -/
def solve : Env Int := do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst Int "x"
  s.assert (← smt! ![double x] = 6)
  s.checkSat (ifSat := s.getValue x)

end

#eval Env.runIO solve   -- 3
```

Without `variable [Ω]`, `def double … : Env (Term Int)` does not compile at all — `failed to
synthesize Ω` — since there is no instance to find. The fix is never to look for one: it is to take
it as a parameter. The alternative of writing everything inline, inside one `Env.runIO do …`, does
work, but nothing in that block can be reused or tested on its own.

`Ω` is a `Prop`, so carrying it everywhere costs nothing at runtime.

## Two layers

Terms come in two flavours, which share the environment, the solver and the sorts.

- **`Cvc.Untyped`**: a `Term` carries no Lean-side sort. It is close to cvc5 itself, and a sort
  mistake is cvc5's to report, at runtime.
- **`Cvc.Typed`**: a `Term α` is indexed by the Lean type its sort denotes — `Term Int`,
  `Term (Set Bool)`, `Term (Int → Bool)`. A sort mistake is a Lean type error, and a model value
  comes back as an `Int`, a `Set Bool`, with nothing to convert.

The two are the same type at runtime: `Typed.Term.erase` goes down for free, and
`Untyped.Term.typeCheck` goes up by checking the term's sort. `open Cvc.Untyped` or
`open Cvc.Typed` selects a layer, along with its spelling of the `smt!` DSL, which writes terms in
something close to Lean's own notation: `smt! i + 2 * j ≤ k ∧ ¬ b`.

## Solving

A `Solver` is created inside an environment with `Solver.new`, and is fed assertions with
`Solver.assert`. `Solver.checkSat` takes one branch per possible answer, and each branch runs in a
monad that only allows what that answer makes meaningful: reading a model is only possible in the
`ifSat` branch, an unsat core only in `ifUnsat`. Those monads are indexed by the solver that
answered, so one solver's model cannot be read through another.

## What to import

This root module imports everything. That is convenient, but each theory's constructors are
generated in a module of their own, per layer, so that a user compiles only the theories and the
layer they import — and `smt!` accepts only the notations of the theories imported. Prefer
importing `Cvc.Typed.Theory.Arith` and friends, or `Cvc.Untyped`, over `Cvc`, once you know
which you need.
-/
