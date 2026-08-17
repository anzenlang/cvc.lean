/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Tests.Logic
import Cvc.Tests.Srt
import Cvc.Tests.Signatures
import Cvc.Tests.Fun
import Cvc.Tests.Untyped.Term.Bool
import Cvc.Tests.Untyped.Term.Arith
import Cvc.Tests.Untyped.Term.BitVec
import Cvc.Tests.Untyped.Term.Array
import Cvc.Tests.Untyped.Term.Set
import Cvc.Tests.Untyped.Term.Bag
import Cvc.Tests.Untyped.Term.Seq
import Cvc.Tests.Untyped.Term.Nullable
import Cvc.Tests.Untyped.Term.Nullable.Arith
import Cvc.Tests.Untyped.Term.String
import Cvc.Tests.Untyped.Term.Regex
import Cvc.Tests.Untyped.Term.Float
import Cvc.Tests.Untyped.Term.FiniteField
import Cvc.Tests.Untyped.Term.Tuple
import Cvc.Tests.Untyped.Term.Relation
import Cvc.Tests.Untyped.Term.Table
import Cvc.Tests.Untyped.Term.Fun
import Cvc.Tests.Untyped.Term.Ext
import Cvc.Tests.Untyped.Solver
import Cvc.Tests.Untyped.Datatype
import Cvc.Tests.Untyped.Grammar
import Cvc.Tests.Untyped.Synth
import Cvc.Tests.Untyped.BVar
import Cvc.Tests.Untyped.Subst
import Cvc.Tests.Untyped.Value
import Cvc.Tests.Typed.Term.Bool
import Cvc.Tests.Typed.Term.Arith
import Cvc.Tests.Typed.Term.BitVec
import Cvc.Tests.Typed.Term.Array
import Cvc.Tests.Typed.Term.Set
import Cvc.Tests.Typed.Term.Bag
import Cvc.Tests.Typed.Term.Seq
import Cvc.Tests.Typed.Term.Nullable
import Cvc.Tests.Typed.Term.Nullable.Arith
import Cvc.Tests.Typed.Term.Nullable.Theories
import Cvc.Tests.Typed.Term.String
import Cvc.Tests.Typed.Term.Regex
import Cvc.Tests.Typed.Term.Float
import Cvc.Tests.Typed.Term.FiniteField
import Cvc.Tests.Typed.Term.Tuple
import Cvc.Tests.Typed.Term.Relation
import Cvc.Tests.Typed.Term.Table
import Cvc.Tests.Typed.Term.Fun
import Cvc.Tests.Typed.Term.Ext
import Cvc.Tests.Typed.Solver
import Cvc.Tests.Typed.Datatype
import Cvc.Tests.Typed.Grammar
import Cvc.Tests.Typed.Synth
import Cvc.Tests.Typed.BVar
import Cvc.Tests.Typed.Subst
import Cvc.Tests.Typed.Value



/-! # Test suite

Run with `lake build Cvc.Tests`.

Deliberately *not* imported by `Cvc`, so that depending on the library does not drag its
tests in. That also means `lake test` does not cover it: the `cvcTests` library globs `Cvc.Tests`,
and picking these up as well would take adding `Cvc.Tests` to that glob in `lakefile.lean`.

Layout mirrors the modules under test:

- `Signatures` — pins the generated signatures of both layers, and the definitional facts
  (`bvConcat`'s size arithmetic, `neg`'s generality over `IsArith`);
- `Untyped/`, `Typed/` — one module per theory, plus `Ext` for that layer's `smt!` DSL.
-/
