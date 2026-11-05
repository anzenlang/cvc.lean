/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Set specification

Note the operand order of `setMember` and `setInsert`: cvc5 takes the *element* first and the
set last.
-/
namespace Cvc public section

/-- Set membership. -/
op% setMember {α} (elm : α) (s : set α) : bool := SET_MEMBER infixr "∈" 50

/-- Subset predicate. -/
op% setSubset {α} (lft rgt : set α) : bool := SET_SUBSET infixr "⊆" 50

/-- Emptiness tester. -/
op% setIsEmpty {α} (s : set α) : bool := SET_IS_EMPTY

/-- Singleton tester. -/
op% setIsSingleton {α} (s : set α) : bool := SET_IS_SINGLETON

/-- The singleton set containing one element. -/
op% setSingleton {α} (elm : α) : set α := SET_SINGLETON

/-- Inserts an element into a set. -/
op% setInsert {α} (elm : α) (s : set α) : set α := SET_INSERT

/-- Set union. -/
op% setUnion {α} (lft rgt : set α) : set α := SET_UNION infixl "∪" 65 nary

/-- Set intersection. -/
op% setInter {α} (lft rgt : set α) : set α := SET_INTER infixl "∩" 70 nary

/-- Set difference. -/
op% setMinus {α} (lft rgt : set α) : set α := SET_MINUS infixl "∖" 65 nary

/-- Set complement, relative to the universe set of the element sort. -/
op% setComplement {α} (s : set α) : set α := SET_COMPLEMENT

/-- Cardinality. -/
op% setCard {α} (s : set α) : int := SET_CARD

/-- An unspecified element of a non-empty set. -/
op% setChoose {α} (s : set α) : α := SET_CHOOSE



/-! ## Higher-order operators -/

/-- The image of a set under a function. -/
op% setMap {α β} (f : fn α β) (s : set α) : set β := SET_MAP

/-- The elements of a set satisfying a predicate. -/
op% setFilter {α} (p : fn α bool) (s : set α) : set α := SET_FILTER

/-- Folds a binary function over a set, from an initial value. -/
op% setFold {α β} (f : fn α (fn β β)) (init : β) (s : set α) : β := SET_FOLD

/-- Whether every element of a set satisfies a predicate. -/
op% setAll {α} (p : fn α bool) (s : set α) : bool := SET_ALL

/-- Whether some element of a set satisfies a predicate. -/
op% setSome {α} (p : fn α bool) (s : set α) : bool := SET_SOME

/-! ## Constants

Built by a `TermManager` method rather than by applying a kind, so the sort-erased constructor
takes the sort it builds while the typed one recovers it from its index.
-/

/-- The empty set. -/
op% setEmpty {α} : set α := SET_EMPTY tm mkEmptySet

/-- The set containing every element of the sort. -/
op% setUniverse {α} : set α := SET_UNIVERSE tm mkUniverseSet
