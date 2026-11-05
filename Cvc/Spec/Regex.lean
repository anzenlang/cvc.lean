/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Regular-expression specification

`reLoop` and `reRepeat` are indexed.
-/
namespace Cvc public section

/-- Concatenation. -/
op% reConcat (lft rgt : regex) : regex := REGEXP_CONCAT nary

/-- Union. -/
op% reUnion (lft rgt : regex) : regex := REGEXP_UNION nary

/-- Intersection. -/
op% reInter (lft rgt : regex) : regex := REGEXP_INTER nary

/-- Difference. -/
op% reDiff (lft rgt : regex) : regex := REGEXP_DIFF

/-- Kleene star. -/
op% reStar (re : regex) : regex := REGEXP_STAR

/-- One or more repetitions. -/
op% rePlus (re : regex) : regex := REGEXP_PLUS

/-- Zero or one repetition. -/
op% reOpt (re : regex) : regex := REGEXP_OPT

/-- The regular expression matching any character between two one-character bounds. -/
op% reRange (lo hi : string) : regex := REGEXP_RANGE

/-- Complement. -/
op% reComplement (re : regex) : regex := REGEXP_COMPLEMENT



/-! ## Indexed operators -/

/-- Between `lo` and `hi` repetitions. -/
op% reLoop [lo hi] (re : regex) : regex := REGEXP_LOOP

/-- Exactly the given number of repetitions. -/
op% reRepeat [count] (re : regex) : regex := REGEXP_REPEAT

/-! ## Constants

These take no sort: their result is `RegLan` whatever the context.
-/

/-- The regular expression matching every string. -/
op% reAll : regex := REGEXP_ALL tm mkRegexpAll

/-- The regular expression matching every one-character string. -/
op% reAllChar : regex := REGEXP_ALLCHAR tm mkRegexpAllchar

/-- The regular expression matching nothing. -/
op% reNone : regex := REGEXP_NONE tm mkRegexpNone
