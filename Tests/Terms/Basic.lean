/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Tests.Basic



namespace Cvc.Test



Term.test!

with
  let boo ← Term.bool false
  let seven ← Term.int 7
  let five ← Term.int 5
  let ten ← Term.int 10
  show[", "| boo, seven, five, ten]


[Term.equal]
  let equal_7_5_10 ← Term.mkEqual #[seven, five, ten]
  let equal_5_10 ← Term.mkEqual #[five, ten]
  let seven_equal_five ← seven.equal five
  show[equal_7_5_10, equal_5_10, seven_equal_five]
/-- info: boo ↦ false, seven ↦ 7, five ↦ 5, ten ↦ 10

equal_7_5_10 ↦ (and (= 7 5) (= 5 10))
equal_5_10 ↦ (= 5 10)
seven_equal_five ↦ (= 7 5)
-/

[Term.distinct]
  let distinct_7_5_10 ← Term.mkDistinct #[seven, five, ten]
  let distinct_5_10 ← Term.mkDistinct #[five, ten]
  let seven_distinct_five ← seven.distinct five
  show[distinct_7_5_10, distinct_5_10, seven_distinct_five]
/-- info: boo ↦ false, seven ↦ 7, five ↦ 5, ten ↦ 10

distinct_7_5_10 ↦ (distinct 7 5 10)
distinct_5_10 ↦ (distinct 5 10)
seven_distinct_five ↦ (distinct 7 5)
-/

[Term.ite]
  let if_boo_seven_five ← boo.ite seven five
  show[if_boo_seven_five]
/-- info: boo ↦ false, seven ↦ 7, five ↦ 5, ten ↦ 10

if_boo_seven_five ↦ (ite false 7 5)
-/

[Term.mul]
  let mul_7_5_10 ← Term.mkMul #[seven, five, ten]
  let seven_mul_five ← seven.mul five
  show[mul_7_5_10, seven_mul_five]
/-- info: boo ↦ false, seven ↦ 7, five ↦ 5, ten ↦ 10

mul_7_5_10 ↦ (* 7 5 10)
seven_mul_five ↦ (* 7 5)
-/

[Term.add]
  let add_7_5_10 ← Term.mkAdd #[seven, five, ten]
  let seven_add_five ← seven.add five
  show[add_7_5_10, seven_add_five]
/-- info: boo ↦ false, seven ↦ 7, five ↦ 5, ten ↦ 10

add_7_5_10 ↦ (+ 7 5 10)
seven_add_five ↦ (+ 7 5)
-/
