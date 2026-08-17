/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Bag specification

As for sets, `bagMember`, `bagCount` and `bagMake` take the element first.
-/
namespace Cvc public section

/-- Bag membership. -/
op% bagMember {α} (elm : α) (b : bag α) : bool := BAG_MEMBER

/-- Inclusion predicate: every multiplicity on the left is at most the one on the right. -/
op% bagSubbag {α} (lft rgt : bag α) : bool := BAG_SUBBAG

/-- The bag containing one element with the given multiplicity. -/
op% bagMake {α} (elm : α) (count : int) : bag α := BAG_MAKE

/-- Multiplicity of an element. -/
op% bagCount {α} (elm : α) (b : bag α) : int := BAG_COUNT

/-- Cardinality, counting multiplicities. -/
op% bagCard {α} (b : bag α) : int := BAG_CARD

/-- Duplicate removal, yielding a bag whose multiplicities are all at most one. -/
op% bagSetof {α} (b : bag α) : bag α := BAG_SETOF

/-- An unspecified element of a non-empty bag. -/
op% bagChoose {α} (b : bag α) : α := BAG_CHOOSE

/-- Union taking the maximum of the multiplicities. -/
op% bagUnionMax {α} (lft rgt : bag α) : bag α := BAG_UNION_MAX nary

/-- Union adding the multiplicities. -/
op% bagUnionDisjoint {α} (lft rgt : bag α) : bag α := BAG_UNION_DISJOINT infixl "⊎" 65 nary

/-- Intersection taking the minimum of the multiplicities. -/
op% bagInterMin {α} (lft rgt : bag α) : bag α := BAG_INTER_MIN nary

/-- Difference subtracting the multiplicities. -/
op% bagDifferenceSubtract {α} (lft rgt : bag α) : bag α := BAG_DIFFERENCE_SUBTRACT

/-- Difference removing every element occurring on the right. -/
op% bagDifferenceRemove {α} (lft rgt : bag α) : bag α := BAG_DIFFERENCE_REMOVE



/-! ## Higher-order operators -/

/-- The image of a bag under a function. -/
op% bagMap {α β} (f : fn α β) (b : bag α) : bag β := BAG_MAP

/-- The elements of a bag satisfying a predicate, with their multiplicities. -/
op% bagFilter {α} (p : fn α bool) (b : bag α) : bag α := BAG_FILTER

/-- Folds a binary function over a bag, from an initial value. -/
op% bagFold {α β} (f : fn α (fn β β)) (init : β) (b : bag α) : β := BAG_FOLD

/-- Whether every element of a bag satisfies a predicate. -/
op% bagAll {α} (p : fn α bool) (b : bag α) : bool := BAG_ALL

/-- Whether some element of a bag satisfies a predicate. -/
op% bagSome {α} (p : fn α bool) (b : bag α) : bool := BAG_SOME

/-- Partitions a bag into the equivalence classes of a binary predicate.

The predicate is expected to be an equivalence relation on the bag's elements; the result holds
one bag per class. Its sort is `Bag (Bag α)`, which is why the element sort needs an order.
-/
op% bagPartition {α} (p : fn α (fn α bool)) (b : bag α) : bag (bag α) := BAG_PARTITION

/-! ## Constants -/

/-- The empty bag. -/
op% bagEmpty {α} : bag α := BAG_EMPTY tm mkEmptyBag
