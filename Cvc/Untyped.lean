/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core
public import Cvc.Untyped.Grammar
public import Cvc.Untyped.Proof
public import Cvc.Untyped.Synth
public import Cvc.Untyped.Theory
public import Cvc.Untyped.Extra
public import Cvc.Untyped.View

/-! # The sort-erased layer

A `Cvc.Untyped.Term` carries no Lean-side sort: terms of every sort share one type, and a sort
mistake, such as `and` applied to an integer, is reported by cvc5 at run time. `Cvc.Typed` is the
same API over terms indexed by the Lean type their sort denotes, where such mistakes do not compile;
`Term.typeCheck` moves a term from this layer to that one, and `toUntyped` moves it back.

`open Cvc.Untyped` selects this layer's notations: `smt!`, `smt.grammar!` and `regex!`.
-/
