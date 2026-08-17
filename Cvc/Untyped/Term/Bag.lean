/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Srt

public import Cvc.Srt

import all Cvc.Basic.Env
import all Cvc.Untyped.Term.Defs

public import Cvc.Untyped.Term.Defs
public import Cvc.Ext
public import Cvc.Untyped.Term.Value
public import Cvc.Types.Bag
public import Cvc.Untyped.Term.Arith
public import Cvc.Gen
public import Cvc.Spec.Bag



/-! # Generated Bag constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

gen_untyped% from Cvc.Spec.Bag



/-! ## Values

A `Cvc.Bag` denotes an SMT bag: the empty bag, unioned with one singleton bag per element, each
carrying that element's multiplicity.
-/

section variable [Ord α] [ToTyp α]

/-- The bag term denoting a bag of values. -/
def mkBagValue [ValueToTerm α] (bag : Cvc.Bag α) : Env Term := do
  let empty ← Srt.of α >>= bagEmpty
  bag.foldlM (init := empty) fun acc elem count => do
    let elem ← mkValue elem
    let count ← mkInt count
    bagMake elem count >>= bagUnionMax acc

/-- The bag of values a constant bag term denotes.

A bag value is a spine of unions over singletons, so this walks the term's kind. cvc5 only ever
produces `BAG_UNION_DISJOINT` spines in a model, but the other combinators are recognised as
unsupported rather than reported as a sort mismatch.
-/
partial def getBagValue [TermToValue α] (term : Term) : Env (Cvc.Bag α) := do
  let kind ← term.getKind
  match kind with
  | .BAG_EMPTY => return Cvc.Bag.empty
  | .BAG_MAKE =>
    let ⟨kids, _⟩ ← term.getSizedKids 2
    return Cvc.Bag.empty.insert (← getValue kids[0]) (← getValue kids[1])
  | .BAG_UNION_MAX | .BAG_UNION_DISJOINT =>
    let ⟨kids, _⟩ ← term.getSizedKids 2
    let lft : Cvc.Bag α ← getBagValue kids[0]
    let rgt : Cvc.Bag α ← getBagValue kids[1]
    return rgt.foldl (init := lft) fun acc elem count =>
      acc.insert elem (max count (acc.getD elem 0))
  | .BAG_INTER_MIN | .BAG_DIFFERENCE_SUBTRACT | .BAG_DIFFERENCE_REMOVE =>
    throwTodo s!"bag-value reconstruction for term kind `{kind}`"
  | _ => throwUser s!"expected a constant bag term, got one of kind `{kind}`"

instance [ValueToTerm α] : ValueToTerm (Cvc.Bag α) := ⟨mkBagValue⟩
instance [TermToValue α] : TermToValue (Cvc.Bag α) := ⟨getBagValue⟩

end
