/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Types.Set
public import Cvc.Types.Bag
public import Cvc.Types.Array
public import Cvc.Types.Tuple
public import Cvc.Types.Relation
public import Cvc.Types.Record
public import Cvc.Types.Float
public import Cvc.Types.FiniteField
public import Cvc.Types.Denote



/-! # The Lean types denoting SMT sorts

The Lean types that sorts denote — sets, bags, total maps, floats, finite-field elements, tuples,
relations, records — each with its `ToTyp` instance and the Lean-side operations it needs. They are
shared by both layers. Converting a value to a term and back is done by each theory's module, such
as `Cvc.Typed.Theory.Set`.
-/
