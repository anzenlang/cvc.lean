/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Finite-field specification

Arithmetic in a prime field, whose modulus is the
sort's index.
-/
namespace Cvc public section

/-- Addition. -/
op% ffAdd {k : size} (lft rgt : finiteField k) : finiteField k := FINITE_FIELD_ADD nary

/-- Multiplication. -/
op% ffMul {k : size} (lft rgt : finiteField k) : finiteField k := FINITE_FIELD_MULT nary

/-- Negation. -/
op% ffNeg {k : size} (ff : finiteField k) : finiteField k := FINITE_FIELD_NEG

/-- Bit-sum, interpreting its arguments as bits. -/
op% ffBitsum {k : size} (lft rgt : finiteField k) : finiteField k := FINITE_FIELD_BITSUM nary
