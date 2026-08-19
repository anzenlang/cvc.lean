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
import all Cvc.Untyped.Core.Defs

public import Cvc.Ext
public import Cvc.Untyped.Core.Value
public import Cvc.Types.Array
public import Cvc.Gen.Term
public import Cvc.Spec.Array



/-! # Generated Array constructors, sort-erased -/
namespace Cvc.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Spec.Array



/-! ## Values

A `TotalMap` denotes an SMT array: a constant array holding the default element, with one `store`
per binding. Reading one back peels that spine, keeping the *outermost* store for a repeated index
since it is the one that wins.
-/

@[inherit_doc T.isConstArray]
def isConstArray (term : Term) : Bool := T.isConstArray term.toUnsafe


/-- The default element of a constant-array term, if it is one. -/
def getConstArrayBase? (term : Term) : Option Term :=
  let base : Option cvc5.Term := T.getConstArrayBase? term.toUnsafe
  base

section variable [Ord α] [ToTyp α] [ToTyp β]

/-- The array term denoting a total map. -/
def mkArrayValue [ValueToTerm α] [ValueToTerm β] (map : Cvc.TotalMap α β) : Env Term := do
  let idx ← Srt.of α
  let mut term ← mkValue map.defaultElem >>= mkConstArray idx
  for (idx, elem) in map.map do
    term ← store term (← mkValue idx) (← mkValue elem)
  return term

/-- The total map a constant array term denotes. -/
partial def getArrayValue [TermToValue α] [TermToValue β] (term : Term)
: Env (Cvc.TotalMap α β) :=
  peel Std.TreeMap.empty term
where
  peel (acc : Std.TreeMap α β) (term : Term) : Env (Cvc.TotalMap α β) := do
    if term.getKind? = some .STORE then
      let ⟨kids, _⟩ ← term.getSizedKids 3
      let idx : α ← getValue kids[1]
      let elem : β ← getValue kids[2]
      peel (if acc.contains idx then acc else acc.insert idx elem) kids[0]
    else if let some dflt := term.getConstArrayBase? then
      return .mk (← getValue dflt) acc
    else throwUser s!"expected a constant array term, got `{term}`"

instance [ValueToTerm α] [ValueToTerm β] : ValueToTerm (Cvc.TotalMap α β) := ⟨mkArrayValue⟩
instance [TermToValue α] [TermToValue β] : TermToValue (Cvc.TotalMap α β) := ⟨getArrayValue⟩

end
