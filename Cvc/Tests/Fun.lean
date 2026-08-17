/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Term
import Cvc.Untyped.Term
import Cvc.Types.Set
import Cvc.Types.Bag
import Cvc.Types.Array
import Cvc.Types.Float

public meta import Cvc.Typed.Term
public meta import Cvc.Untyped.Term
public meta import Cvc.Types.Set
public meta import Cvc.Types.Bag
public meta import Cvc.Types.Array
public meta import Cvc.Types.Float



/-! # Function sorts

Three things are checked here, in increasing order of how quietly they could go wrong:

1. that a function index renders to the SMT sort it claims to, in particular that currying
   flattens while a higher-order *domain* is preserved;
2. that the generated signatures track the index through application;
3. that applying a function is definitionally well-typed, including partial application.

Term construction and end-to-end solving live in `Tests/{Untyped,Typed}/Fun.lean`.
-/
namespace Cvc.Tests.Fun

open Cvc



/-! ## Sort rendering

A function sort is indexed by a Lean arrow. A curried spine flattens into cvc5's n-ary domain, so
`α → β → γ` is `(-> α β γ)` and *not* `(-> α (-> β γ))`. A function in *domain* position is
genuinely higher-order and stays nested. Those two facts are the whole of the encoding, so both
directions are checked.
-/

/-- info:
unary            : (-> Int Bool)
argument order   : (-> Bool Int)
curried 2        : (-> Int Bool Real)
curried 3        : (-> Int Bool Real Bool)
curried 4        : (-> Int Int Int Int)
higher-order dom : (-> (-> Int Bool) Real)
ho dom, curried  : (-> (-> Int Bool) Real Int)
ho in the middle : (-> Int (-> Int Bool) Real)
sets and bags    : (-> (Set Int) (Bag Int))
array domain     : (-> (Array Int Int) Bool)
bit-vec and seq  : (-> (_ BitVec 4) (Seq Int))
string and regex : (-> String RegLan)
float and mode   : (-> (_ FloatingPoint 8 24) RoundingMode)
-/
#guard_msgs in #eval Env.runIO do
  println! "unary            : {← Srt.of (Int → Bool)}"
  println! "argument order   : {← Srt.of (Bool → Int)}"
  println! "curried 2        : {← Srt.of (Int → Bool → Rat)}"
  println! "curried 3        : {← Srt.of (Int → Bool → Rat → Bool)}"
  println! "curried 4        : {← Srt.of (Int → Int → Int → Int)}"
  println! "higher-order dom : {← Srt.of ((Int → Bool) → Rat)}"
  println! "ho dom, curried  : {← Srt.of ((Int → Bool) → Rat → Int)}"
  println! "ho in the middle : {← Srt.of (Int → (Int → Bool) → Rat)}"
  println! "sets and bags    : {← Srt.of ((Cvc.Set Int) → (Cvc.Bag Int))}"
  println! "array domain     : {← Srt.of ((Cvc.TotalMap Int Int) → Bool)}"
  println! "bit-vec and seq  : {← Srt.of ((BitVec 4) → (Array Int))}"
  println! "string and regex : {← Srt.of (String → Cvc.Regex)}"
  println! "float and mode   : {← Srt.of ((Cvc.Float 8 24) → Cvc.Float.RoundingMode)}"

-- currying is not associativity: a function in domain position is a different sort from the
-- curried spine with the same leaves, so this prints nothing
#guard_msgs in #eval Env.runIO do
  let curried ← Srt.of (Int → Bool → Rat)
  let higherOrder ← Srt.of ((Int → Bool) → Rat)
  if curried.beq higherOrder then println! "sorts collapsed, which they must not"



/-! ## Generated signatures -/

section signatures
variable [Ω]

/-- info: @Typed.Term.apply : [inst : Ω] → {α β : Type} → Typed.Term (α → β) → Typed.Term α → Env (Typed.Term β) -/
#guard_msgs in #check @Cvc.Typed.Term.apply

/-- info: @Typed.Term.apply2 : [inst : Ω] →
  {α β γ : Type} → Typed.Term (α → β → γ) → Typed.Term α → Typed.Term β → Env (Typed.Term γ) -/
#guard_msgs in #check @Cvc.Typed.Term.apply2

/-- info: @Typed.Term.apply3 : [inst : Ω] →
  {α β γ δ : Type} → Typed.Term (α → β → γ → δ) → Typed.Term α → Typed.Term β → Typed.Term γ → Env (Typed.Term δ) -/
#guard_msgs in #check @Cvc.Typed.Term.apply3

/-- info: @Typed.Term.applyHo : [inst : Ω] → {α β : Type} → Typed.Term (α → β) → Typed.Term α → Env (Typed.Term β) -/
#guard_msgs in #check @Cvc.Typed.Term.applyHo

-- erasure drops the function sort along with every other shape
/-- info: @Untyped.Term.apply2 : [inst : Ω] → Untyped.Term → Untyped.Term → Untyped.Term → Env Untyped.Term -/
#guard_msgs in #check @Cvc.Untyped.Term.apply2

-- `Ord` is required on both element types, since the result set is keyed by the codomain
/-- info: @Typed.Term.setMap : [inst : Ω] →
  {α β : Type} →
    [inst_1 : Ord α] → [inst_2 : Ord β] → Typed.Term (α → β) → Typed.Term (Set α) → Env (Typed.Term (Set β)) -/
#guard_msgs in #check @Cvc.Typed.Term.setMap

-- …but a fold's accumulator never keys a container, so it needs no `Ord`
/-- info: @Typed.Term.setFold : [inst : Ω] →
  {α β : Type} → [inst_1 : Ord α] → Typed.Term (α → β → β) → Typed.Term β → Typed.Term (Set α) → Env (Typed.Term β) -/
#guard_msgs in #check @Cvc.Typed.Term.setFold

/-- info: @Typed.Term.setAll : [inst : Ω] →
  {α : Type} → [inst_1 : Ord α] → Typed.Term (α → Bool) → Typed.Term (Set α) → Env (Typed.Term Bool) -/
#guard_msgs in #check @Cvc.Typed.Term.setAll

/-- info: @Typed.Term.bagFold : [inst : Ω] →
  {α β : Type} → [inst_1 : Ord α] → Typed.Term (α → β → β) → Typed.Term β → Typed.Term (Bag α) → Env (Typed.Term β) -/
#guard_msgs in #check @Cvc.Typed.Term.bagFold

end signatures



/-! ## Application is definitionally well-typed

Each of these pins the index the application produces. They typecheck by delegation, with no
coercion anywhere.
-/

section discipline
open Cvc.Typed (Term)
open Cvc.Typed.Term

variable [Ω]
  (f : Term (Int → Bool))
  (g : Term (Int → Bool → Rat))
  (h : Term (Int → Bool → Rat → Int))
  (hof : Term ((Int → Bool) → Rat))
  (i : Term Int) (b : Term Bool) (r : Term Rat)

/-- Saturating a one-argument function lands in its codomain. -/
example : Env (Term Bool) := apply f i

/-- Saturating a two-argument function consumes both arguments at once. -/
example : Env (Term Rat) := apply2 g i b

/-- …and a three-argument one, all three. -/
example : Env (Term Int) := apply3 h i b r

/-- Applying one argument of a curried function leaves a *function*-indexed term. -/
example : Env (Term (Bool → Rat)) := applyHo g i

/-- Chaining single applications reaches the same codomain as saturating. -/
example : Env (Term Rat) := do applyHo (← applyHo g i) b

/-- The chained and saturating forms agree on their index. -/
example : Env (Term Int) := do applyHo (← applyHo (← applyHo h i) b) r

/-- A function passed as an argument to a higher-order function. -/
example : Env (Term Rat) := apply hof f

/-- The higher-order argument keeps its own index, so it can still be applied. -/
example : Env (Term Bool) := apply f i

end discipline

section containers
open Cvc.Typed (Term)
open Cvc.Typed.Term

variable [Ω]
  (p : Term (Int → Bool)) (m : Term (Int → Int))
  (acc : Term (Int → Rat → Rat))
  (s : Term (Cvc.Set Int)) (bg : Term (Cvc.Bag Int))
  (z : Term Rat)

/-- Mapping rewrites the element index. -/
example : Env (Term (Cvc.Set Int)) := setMap m s

/-- Filtering preserves it. -/
example : Env (Term (Cvc.Set Int)) := setFilter p s

/-- A predicate over a set lands in `Bool`. -/
example : Env (Term Bool) := setAll p s

/-- Folding lands in the accumulator's index, which need not be the element's. -/
example : Env (Term Rat) := setFold acc z s

/-- The same holds for bags. -/
example : Env (Term Rat) := bagFold acc z bg

/-- Partitioning nests the container: the result is a bag *of bags*, which is what makes the
element sort's `Ord` instance load-bearing. -/
example (eq : Term (Int → Int → Bool)) : Env (Term (Cvc.Bag (Cvc.Bag Int))) :=
  bagPartition eq bg
example : Env (Term (Cvc.Bag Int)) := bagFilter p bg
example : Env (Term Bool) := bagSome p bg

end containers
