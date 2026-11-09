/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Sequence specification

Sequences are indexed by their element sort, and render as `Array α` on the Lean side.
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

/-- The element at `idx`; unspecified out of bounds. -/
op% seqNth {α} (s : seq α) (idx : int) : α := SEQ_NTH

/-- The sub-sequence of length `len` starting at `idx`; empty when out of range. -/
op% seqExtract {α} (s : seq α) (idx len : int) : seq α := SEQ_EXTRACT

/-- Overwrites `s` from `idx` with `repl`, keeping its length; `s` if `idx` is out of range. -/
op% seqUpdate {α} (s : seq α) (idx : int) (repl : seq α) : seq α := SEQ_UPDATE

/-- Index of the first occurrence of `sub` in `s` at or after `start`, or `-1`. -/
op% seqIndexof {α} (s sub : seq α) (start : int) : int := SEQ_INDEXOF

/-- Replaces the first occurrence of a sub-sequence. -/
op% seqReplace {α} (s pat repl : seq α) : seq α := SEQ_REPLACE

/-- Replaces every occurrence of a sub-sequence. -/
op% seqReplaceAll {α} (s pat repl : seq α) : seq α := SEQ_REPLACE_ALL

/-- Reversal. -/
op% seqRev {α} (s : seq α) : seq α := SEQ_REV

/-- Whether `s` contains `sub`. -/
op% seqContains {α} (s sub : seq α) : bool := SEQ_CONTAINS

/-- Whether `pre` is a prefix of `s`. -/
op% seqPrefix {α} (pre s : seq α) : bool := SEQ_PREFIX

/-- Whether `suf` is a suffix of `s`. -/
op% seqSuffix {α} (suf s : seq α) : bool := SEQ_SUFFIX

/-! ## Constructors -/

/-- The empty sequence of elements of sort `α`. -/
op% mkEmptySeq {α} : seq α := CONST_SEQUENCE tmSortOf mkEmptySequence α
-- The `tmSortOf` clause is about cvc5's method, not the generated signature: every constructor of a
-- polymorphic sort takes the element sorts, but `mkEmptySequence` happens to want that sort
-- directly where `mkEmptySet` wants the set sort built from it.
