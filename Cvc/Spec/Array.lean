/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Array specification

`select`/`store` mirror SMT-LIB; `eqRange`, experimental in cvc5, compares two arrays over an index
range.
-/
namespace Cvc public section

/-- Reads the element stored at an index. -/
op% select {ι κ} (arr : array ι κ) (idx : ι) : κ := SELECT

/-- Writes an element at an index, yielding the updated array. -/
op% store {ι κ} (arr : array ι κ) (idx : ι) (elm : κ) : array ι κ := STORE

/-- Equality of two arrays at every index from `lo` to `hi`, both included.

Needs cvc5's `arrays-exp` option, and an integer, real, bit-vector or floating-point index.
-/
op% eqRange {ι κ} (lft rgt : array ι κ) (lo hi : ι) : bool := EQ_RANGE

/-! ## Constructors -/

/-- The array mapping every index, of sort `ι`, to `default`. -/
op% mkConstArray {ι κ} (default : κ) : array ι κ := CONST_ARRAY tm mkConstArray
