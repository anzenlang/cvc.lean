/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Defs
public import Cvc.Spec.Decl
public import Cvc.Spec.Bool
public import Cvc.Spec.Arith
public import Cvc.Spec.BitVec
public import Cvc.Spec.Array
public import Cvc.Spec.Set
public import Cvc.Spec.Bag
public import Cvc.Spec.Seq
public import Cvc.Spec.String
public import Cvc.Spec.Regex
public import Cvc.Spec.Float
public import Cvc.Spec.FiniteField
public import Cvc.Spec.Fun
public import Cvc.Spec.Sep



/-! # The term-creation specification

One `op%` entry per term kind, written in the typed form, split by theory. Nothing is generated
here: entries are registered in `opSpecExt` and consumed by `gen_untyped%`/`gen_typed%` in the
per-theory modules under `Cvc/Untyped/` and `Cvc/Typed/`.

`Spec/Defs.lean` holds the data — shapes, sizes, notations, `OpSpec` and the extension —
and `Spec/Decl.lean` the `op%` command that populates it. Everything else in this directory is
specification, one module per theory.

This root aggregates them for convenience. A generation site imports only the theory it generates,
which is what keeps a consumer from compiling specifications it never uses.
-/
