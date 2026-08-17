/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Term
public import Cvc.Untyped.Solver
public import Cvc.Untyped.Datatype
public import Cvc.Untyped.Grammar
public import Cvc.Untyped.Synth



/-! # The sort-erased layer

One directory per part of the API being lifted; `Untyped/Term/` is term creation and
`Untyped/Solver.lean` is the solver.
-/
