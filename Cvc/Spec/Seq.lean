/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Sequence specification

Sequences are indexed by their element sort, and render as
`Array α` on the Lean side.
-/
namespace Cvc public section

/-- The one-element sequence. -/
op% seqUnit {α} (elm : α) : seq α := SEQ_UNIT

/-- Concatenation. -/
op% seqConcat {α} (lft rgt : seq α) : seq α := SEQ_CONCAT infixl "++" 62 nary

/-- Length. -/
op% seqLength {α} (s : seq α) : int := SEQ_LENGTH

/-- The one-element sequence at an index, or the empty sequence if out of bounds. -/
op% seqAt {α} (s : seq α) (idx : int) : seq α := SEQ_AT

/-- The element at an index. -/
op% seqNth {α} (s : seq α) (idx : int) : α := SEQ_NTH

/-- The sub-sequence of the given length, starting at the given index. -/
op% seqExtract {α} (s : seq α) (idx len : int) : seq α := SEQ_EXTRACT

/-- Replaces the sub-sequence starting at an index. -/
op% seqUpdate {α} (s : seq α) (idx : int) (repl : seq α) : seq α := SEQ_UPDATE

/-- Index of the first occurrence of a sub-sequence at or after a starting index. -/
op% seqIndexof {α} (s sub : seq α) (start : int) : int := SEQ_INDEXOF

/-- Replaces the first occurrence of a sub-sequence. -/
op% seqReplace {α} (s pat repl : seq α) : seq α := SEQ_REPLACE

/-- Replaces every occurrence of a sub-sequence. -/
op% seqReplaceAll {α} (s pat repl : seq α) : seq α := SEQ_REPLACE_ALL

/-- Reversal. -/
op% seqRev {α} (s : seq α) : seq α := SEQ_REV

/-- Containment. -/
op% seqContains {α} (s sub : seq α) : bool := SEQ_CONTAINS

/-- Prefix predicate: whether the first sequence is a prefix of the second. -/
op% seqPrefix {α} (pre s : seq α) : bool := SEQ_PREFIX

/-- Suffix predicate: whether the first sequence is a suffix of the second. -/
op% seqSuffix {α} (suf s : seq α) : bool := SEQ_SUFFIX

/-! ## Constructors -/

/-- The empty sequence.

The `tmSortOf` clause is about cvc5's method, not the generated signature: every constructor of a
polymorphic sort takes the element sorts, but `mkEmptySequence` happens to want that sort directly
where `mkEmptySet` wants the set sort built from it.
-/
op% mkEmptySeq {α} : seq α := CONST_SEQUENCE tmSortOf mkEmptySequence α
