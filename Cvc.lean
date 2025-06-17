/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic
import Cvc.Logic
import Cvc.Option
import Cvc.Srt
import Cvc.Defs
import Cvc.Term
import Cvc.Actlit
import Cvc.Symbols
import Cvc.State
import Cvc.Sys



/-! # cvc.lean

Lean 4 API for the [cvc5 SMT solver][cvc5] with a strong concern for ergonomics and type-safety.
Cvc5 is heavily based on the [SMT-LIB standard][smtlib] which the documentation of this library will
frequently reference.

The general workflow is to build strongly-typed `Cvc.Term`-s of some SMT-LIB sort `Srt`, in
particular `Cvc.Formula`s, in the term builder monad `Cvc.Term.Build` (does not allow interacting
with the solvers, only building terms). Terms in this monadic environment can then be used in the
`Cvc.Smt` monad which does allow interactions with cvc5, in particular
- `Cvc.Smt.assert` which asserts a formula in the underlying (cvc5) solver;
- `Cvc.Smt.checkSat`, `Cvc.Smt.checkSatAnd`, and other variants that check whether the assertions
  are *satisfiable*;

Check-sat-result-specific SMT-LIB commands are strongly typed: (un)sat-specific commands are only
accessible through the sat-specific `Cvc.Smt.Sat` (`Cvc.Smt.Unsat`) monad; see for instance
`Cvc.Smt.Sat.getValue` and `Cvc.Smt.Unsat.getProof`.

Mode-specific monadic code can only run by passing it to `Cvc.Smt.checkSatAnd` *via* its `ifSat`,
`ifUnsat`, and `ifUnknown` arguments.

```lean
def run [Monad m]
  (mySatCode : Cvc.Smt.Sat m α)
  (myUnsatCode : Cvc.Smt.Unsat m α)
  (myUnknownCode : Cvc.Smt.Unknown m α)
: Cvc.Smt α :=
  Cvc.Smt.checkSatAnd (ifSat := mySatCode) (ifUnsat := myUnsatCode) (ifUnknown := myUnknownCode)

-- All three parameters default to producing an unexpected-check-sat-result error.
--
-- For instance, the following will produce an error saying that the *unknown* check-sat result was
-- not expected if cvc5's check-sat produces *unknown*.
def run [Monad m]
  (mySatCode : Cvc.Smt.Sat m α)
  (myUnsatCode : Cvc.Smt.Unsat m α)
: Cvc.Smt α :=
  Cvc.Smt.checkSatAnd (ifSat := mySatCode) (ifUnsat := myUnsatCode)
```

This guarantees that sat/unsat/unknown-specific commands only run when the solver is in the
appropriate mode.

## Top-level modules

- `Cvc.Basic`: basic helpers.
- `Cvc.Logic`: SMT-LIB logic definition and helpers.
- `Cvc.Option`: cvc5's options definition and helpers.
- `Cvc.Srt`: SMT-LIB sort definition and helpers.
- `Cvc.Defs`: strongly-typed `Cvc.Term`s, `Cvc.Term.Build`er, and `Cvc.Smt`-like monadic
  environments and associated SMT-LIB commands including `Cvc.Smt.Sat`, `Cvc.Smt.Unsat`, and
  `Cvc.Smt.Unknown`.
- `Cvc.Term`: extra term-related features such as erased terms and the term DSL.
- `Cvc.Actlit`: activation literal API.
- `Cvc.Symbols`: specification for a collection of SMT symbols, typically used to define a notion of
  state. The main class (`Cvc.Symbols`) supports user-defined strongly-typed symbols structures, as
  well as generic symbols structures such the provided `Cvc.Symbols.ByName` which wraps an `RBMap`
  from symbols names (`String`) to untyped terms.

  See `Cvc.Symbols.Dsl` for easy user-defined strongly-typed symbols structures.
- `Cvc.State`: builds on `Cvc.Symbols` but adds a notion of state, *i.e.* symbol/term/value
  parameterized with an unrolling index `k : Nat`.

  See `Cvc.Symbols.Dsl` for easy user-defined strongly-typed state structures.
- `Cvc.Sys`: transition system `k`-induction API, builds on `Cvc.State`.

  See `Cvc.Symbols.Dsl` for easy user-defined strongly-typed system structures.

[cvc5]: https://cvc5.github.io (cvc5 official github page)

[smtlib]: https://smt-lib.org (SMT-LIB official website)

-/
