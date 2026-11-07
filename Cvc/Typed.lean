/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Core
public import Cvc.Typed.Grammar
public import Cvc.Typed.Proof
public import Cvc.Typed.Synth
public import Cvc.Typed.Theory
public import Cvc.Typed.Extra
public import Cvc.Typed.View



/-! # The typed layer

A `Term α` is indexed by the Lean type its sort denotes — `Term Int`, `Term (Set Bool)`,
`Term (Int → Bool)` — so a sort mistake is a Lean type error, and a value read out of a model comes
back as an `α`. `open Cvc.Typed` selects this layer, and its spelling of `smt!`.

The main entry points:

- `Cvc.Typed.Core`: terms, values, bound variables, the `Solver` and symbol structures;
- `Cvc.Typed.Theory`: the term constructors, one module per theory (`Cvc.Typed.Theory.Arith`, …);
- `Cvc.Typed.Grammar` and `Cvc.Typed.Synth`: grammars and syntax-guided synthesis;
- `Cvc.Typed.View` and `Cvc.Typed.Proof`: taking terms and proofs apart;
- `Cvc.Typed.Extra`: transition systems and bounded model checking.
-/
