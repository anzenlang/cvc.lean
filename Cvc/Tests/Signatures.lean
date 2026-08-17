/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Term
import Cvc.Typed.Term

public meta import Cvc.Untyped.Term
public meta import Cvc.Typed.Term



/-! # Generated signatures

Pinning the signatures is the point of the design, so they are checked rather than merely
exercised. Expected-output docstrings are compared verbatim against Lean's own message rendering,
so they keep its wrapping even past 100 columns.
-/
namespace Cvc.Tests.Signatures

open Cvc

variable [Ω]



/-! ## Erasure

Every shape erases to a plain `Untyped.Term`, so only the arity survives.
-/

/-- info: @Untyped.Term.and : [inst : Ω] → Untyped.Term → Untyped.Term → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.and

/-- info: @Untyped.Term.bvConcat : [inst : Ω] → Untyped.Term → Untyped.Term → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.bvConcat

/-- info: @Untyped.Term.andN : [inst : Ω] →
  (terms : Untyped.Terms) → autoParam (2 ≤ Array.size terms) Untyped.Term.andN._auto_1 → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.andN

/-- info: @Untyped.Term.andN' : [inst : Ω] →
  Untyped.Terms →
    optParam (Env Untyped.Term) (Untyped.Term.mkBool true) →
      optParam (Untyped.Term → Env Untyped.Term) pure → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.andN'



/-! ## Typed indices -/

-- A polymorphic operator whose result shape differs from its arguments'.
/-- info: @Typed.Term.equal : [inst : Ω] → {α : Type} → Typed.Term α → Typed.Term α → Env (Typed.Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.equal

-- The n-ary variant keeps the differing result shape.
/-- info: @Typed.Term.equalN : [inst : Ω] →
  {α : Type} →
    (terms : Typed.Terms α) → autoParam (2 ≤ Array.size terms) Typed.Term.equalN._auto_1 → Env (Typed.Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.equalN

-- A refinement class also pulls in the `ToTyp` binder it is stated over.
/-- info: @Typed.Term.add : [inst : Ω] →
  {α : Type} → [inst_1 : ToTyp α] → [IsArith α] → Typed.Term α → Typed.Term α → Env (Typed.Term α) -/
#guard_msgs in #check @Cvc.Typed.Term.add

/-- info: @Typed.Term.neg : [inst : Ω] → {α : Type} → [inst_1 : ToTyp α] → [IsArith α] → Typed.Term α → Env (Typed.Term α) -/
#guard_msgs in #check @Cvc.Typed.Term.neg

-- Size variables become implicit `Nat`s, and the result index is computed.
/-- info: @Typed.Term.bvConcat : [inst : Ω] →
  {n m : Nat} → Typed.Term (BitVec n) → Typed.Term (BitVec m) → Env (Typed.Term (BitVec (n + m))) -/
#guard_msgs in #check @Cvc.Typed.Term.bvConcat

/-- info: @Typed.Term.bvUlt : [inst : Ω] → {n : Nat} → Typed.Term (BitVec n) → Typed.Term (BitVec n) → Env (Typed.Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.bvUlt



/-! ## Container theories

The `Ord` binder is derived from the shape: it appears exactly for the type variables that index a
`Set`, `Bag` or `TotalMap`.
-/

-- an array operator: `Ord` on the index only, and the element index is read off the array
/-- info: @Typed.Term.select : [inst : Ω] →
  {ι κ : Type} → [inst_1 : Ord ι] → Typed.Term (TotalMap ι κ) → Typed.Term ι → Env (Typed.Term κ) -/
#guard_msgs in #check @Cvc.Typed.Term.select

-- set membership takes the element first, matching cvc5
/-- info: @Typed.Term.setMember : [inst : Ω] →
  {α : Type} → [inst_1 : Ord α] → Typed.Term α → Typed.Term (Set α) → Env (Typed.Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.setMember

-- a sequence renders as `Array`, which needs no `Ord`
/-- info: @Typed.Term.seqNth : [inst : Ω] → {α : Type} → Typed.Term (Array α) → Typed.Term Int → Env (Typed.Term α) -/
#guard_msgs in #check @Cvc.Typed.Term.seqNth

-- floating-point predicates carry two size variables
/-- info: @Typed.Term.fpIsNan : [inst : Ω] → {e s : Nat} → Typed.Term (Float e s) → Env (Typed.Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.fpIsNan

-- a one-bit index written as a literal in the spec
/-- info: @Typed.Term.bvIte : [inst : Ω] →
  {n : Nat} → Typed.Term (BitVec 1) → Typed.Term (BitVec n) → Typed.Term (BitVec n) → Env (Typed.Term (BitVec n)) -/
#guard_msgs in #check @Cvc.Typed.Term.bvIte



/-! ## Indexed operators

Indices are explicit `Nat` arguments ahead of the term arguments, and may take part in the result's
sort. Erasure keeps them — they are what the operator is built from — while dropping the shapes.
-/

/-- info: @Typed.Term.bvExtract : [inst : Ω] →
  (hi lo : Nat) → {n : Nat} → Typed.Term (BitVec n) → Env (Typed.Term (BitVec (hi - lo + 1))) -/
#guard_msgs in #check @Cvc.Typed.Term.bvExtract

/-- info: @Untyped.Term.bvExtract : [inst : Ω] → Nat → Nat → Untyped.Term → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.bvExtract

/-- info: @Typed.Term.bvRepeat : [inst : Ω] →
  (count : Nat) → {n : Nat} → Typed.Term (BitVec n) → Env (Typed.Term (BitVec (n * count))) -/
#guard_msgs in #check @Cvc.Typed.Term.bvRepeat

/-- info: @Typed.Term.intToBv : [inst : Ω] → (size : Nat) → Typed.Term Int → Env (Typed.Term (BitVec size)) -/
#guard_msgs in #check @Cvc.Typed.Term.intToBv

-- an operator with both indices and inferred size variables
/-- info: @Typed.Term.fpOfFp : [inst : Ω] →
  (e s : Nat) → {ei si : Nat} → Typed.Term Float.RoundingMode → Typed.Term (Float ei si) → Env (Typed.Term (Float e s)) -/
#guard_msgs in #check @Cvc.Typed.Term.fpOfFp

/-- info: @Typed.Term.fpOfBits : [inst : Ω] →
  {e s : Nat} →
    Typed.Term (BitVec 1) → Typed.Term (BitVec e) → Typed.Term (BitVec s) → Env (Typed.Term (Float e (s + 1))) -/
#guard_msgs in #check @Cvc.Typed.Term.fpOfBits



-- a nested container: `Ord` is emitted for the element variable, and `Ord (Bag α)` for the
-- result's outer layer is then found by instance resolution
/-- info: @Typed.Term.bagPartition : [inst : Ω] →
  {α : Type} → [inst_1 : Ord α] → Typed.Term (α → α → Bool) → Typed.Term (Bag α) → Env (Typed.Term (Bag (Bag α))) -/
#guard_msgs in #check @Cvc.Typed.Term.bagPartition



/-! ## Constructors

A constructor is built by a `TermManager` method rather than by applying a kind, so its sort is
free in the result. Erasure cannot recover it: the sort-erased signature takes it explicitly while
the typed one computes it from the index. The nullary ones need neither.
-/

/-- info: @Untyped.Term.setEmpty : [inst : Ω] → Srt → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.setEmpty

/-- info: @Typed.Term.setEmpty : [inst : Ω] → {α : Type} → [inst_1 : Ord α] → [ToTyp α] → Env (Typed.Term (Set α)) -/
#guard_msgs in #check @Cvc.Typed.Term.setEmpty

-- a constant whose sort is fixed needs no sort argument in either layer
/-- info: @Untyped.Term.reAll : [inst : Ω] → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.reAll

/-- info: @Typed.Term.reAll : [inst : Ω] → Env (Typed.Term Regex) -/
#guard_msgs in #check @Cvc.Typed.Term.reAll

/-- info: @Typed.Term.pi : [inst : Ω] → Env (Typed.Term Rat) -/
#guard_msgs in #check @Cvc.Typed.Term.pi



-- a result size that is the operator's arity: a literal at fixed arity, the array's size when
-- n-ary, which makes that signature depend on a runtime value
/-- info: @Typed.Term.bvFromBool : [inst : Ω] → Typed.Term Bool → Env (Typed.Term (BitVec 1)) -/
#guard_msgs in #check @Cvc.Typed.Term.bvFromBool

/-- info: @Typed.Term.bvFromBools : [inst : Ω] →
  (terms : Typed.Terms Bool) →
    autoParam (2 ≤ Array.size terms) Typed.Term.bvFromBools._auto_1 → Env (Typed.Term (BitVec (Array.size terms))) -/
#guard_msgs in #check @Cvc.Typed.Term.bvFromBools



/-! ## Index arithmetic and refinement classes hold definitionally -/

open Cvc.Typed (Term)
open Cvc.Typed.Term

/-- The size of a concatenation is the sum of its arguments' sizes, with no coercion. -/
example (a : Term (BitVec 4)) (b : Term (BitVec 6)) : Env (Term (BitVec 10)) :=
  bvConcat a b

/-- `neg` is general over `IsArith`, so it applies at `Rat` as well as at `Int`. -/
example (r : Term Rat) : Env (Term Rat) := neg r

/-- Extraction narrows to `hi - lo + 1` bits. -/
example (u : Term (BitVec 8)) : Env (Term (BitVec 4)) := bvExtract 5 2 u

/-- Repetition multiplies the size. -/
example (u : Term (BitVec 8)) : Env (Term (BitVec 24)) := bvRepeat 3 u

/-- Extension adds to the size. -/
example (u : Term (BitVec 8)) : Env (Term (BitVec 12)) := bvZeroExtend 4 u

/-- Assembling a float adds the significand's hidden bit back. -/
example (sgn : Term (BitVec 1)) (ex : Term (BitVec 8)) (sig : Term (BitVec 23))
: Env (Term (Cvc.Float 8 24)) := fpOfBits sgn ex sig
