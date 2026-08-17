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



/-! # A high-level, safety-oriented API for cvc5

Two layers sit on top of [lean-cvc5](https://github.com/abdoo8080/lean-cvc5): `Cvc.Untyped`, where a
term carries no Lean-side sort information, and `Cvc.Typed`, where `Term α` is indexed by the Lean
type its sort denotes. Both are scoped by the `Ω` class of `Cvc.Basic.Env`, which is what keeps
terms from different cvc5 term managers from ever meeting.

Term constructors are **generated**, not written twice. Each one is described once, in the typed
form, by an `op%` entry under `Cvc/Spec/`; `gen_untyped%` then emits the sort-erased constructor
straight through `runUnsafe` and `gen_typed%` the re-typed one delegating to it. The specification
is compile-time data with no runtime footprint.

The layers come first in the layout and the part of the API being lifted second, so term creation
is `Cvc/Untyped/Term/` and `Cvc/Typed/Term/`, and anything lifted later sits beside them.
Generation happens per theory within those, so a user compiles only the theories, and only the
layer, they import.

This root imports everything. Importing it is convenient, but it gives up the property above:
prefer importing the theory modules you actually use. The test suite, `Cvc.Tests`, is deliberately
not imported here.
-/
