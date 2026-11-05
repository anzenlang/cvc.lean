/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core
public import Cvc.Gen.View
public import Cvc.Untyped.Traverse



/-! # Taking sort-erased terms apart

Everything needed to inspect and rewrite terms: `def.term_view V`, which gathers the view of every
imported theory into one inductive, and the traversals over it, `Term.fold` and `Term.walk` with
the zipper beneath them. Theories are imported separately, and only those imported are viewed:
with this module alone, `V` takes apart the Boolean connectives and has its leaves — values,
symbols, bound variables — and a catch-all for everything else.
-/
