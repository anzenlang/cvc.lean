/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # Boolean and sort-generic specification

The connectives, and the operators that are generic in the sort they operate
on: `equal` and `distinct`, whose result is `Bool` whatever their arguments,
and `ite`, which takes its own sort from its branches.
-/
namespace Cvc public section

/-! ## Constructors -/

/-- The `true` term. -/
op% mkTrue : bool := CONST_BOOLEAN tm mkTrue

/-- The `false` term. -/
op% mkFalse : bool := CONST_BOOLEAN tm mkFalse

/-- A boolean literal. -/
op% mkBool (b :! Bool) : bool := CONST_BOOLEAN tm mkBoolean

/-- A symbol of the given sort: a fresh uninterpreted constant. -/
op% mkSymbol {α} (name :! String) : α := CONSTANT tm mkConst

-- the bound-variable constructor is *not* specified here: its result is a `BVar`, not a `Term`,
-- and a shape cannot say so. It is hand-written in `Cvc/{Untyped,Typed}/BVar.lean`, beside
-- the type it produces.



/-! ## Connectives and equality -/

/-- Binary equality. -/
op% equal {α} (lft rgt : α) : bool := EQUAL infixr "=" 50 unit true

/-- Binary pairwise inequality. -/
op% distinct {α} (lft rgt : α) : bool := DISTINCT infixr "≠" 50 nary

/-- Logical negation. -/
op% not (boolTerm : bool) : bool := NOT prefix "¬" 1024 40

/-- Binary implication. -/
op% implies (lft rgt : bool) : bool := IMPLIES infixr "→" 25 nary

/-- Binary conjunction. -/
op% and (lft rgt : bool) : bool := AND infixr "∧" 35 unit true

/-- Binary disjunction. -/
op% or (lft rgt : bool) : bool := OR infixr "∨" 30 unit false

/-- Binary exclusive disjunction. -/
op% xor (lft rgt : bool) : bool := XOR infixl "⊻" 30 unit false

/-- If-then-else from condition, then-branch and else-branch. -/
op% ite {α} (cnd : bool) (thn els : α) : α := ITE
