/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Tests.Basic



namespace Cvc.Test

open scoped Cvc.Term.Dsl



Term.test!

with
  let boo ← smt! false
  let not_boo ← boo.not
  let seven ← smt! 7
  let five ← smt! 5
  let ten ← smt! 10
  show[", "| boo, not_boo, seven, five, ten]

[Term.ite]
  let if_boo_seven_five ← smt!
    if boo then seven else five
  show[if_boo_seven_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

if_boo_seven_five ↦ (ite false 7 5)
-/

[Term.equal]
  let equal_7_5_10 ← smt! =[seven, five, ten]
  let equal_5_10 ← smt! five = ten
  let seven_equal_five ← smt! seven = five
  show[equal_7_5_10, equal_5_10, seven_equal_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

equal_7_5_10 ↦ (and (= 7 5) (= 5 10))
equal_5_10 ↦ (= 5 10)
seven_equal_five ↦ (= 7 5)
-/

[Term.and]
  let equal_7_5_10 ← smt! =[seven, five, ten]
  let equal_5_10 ← smt! five = ten
  let seven_equal_five ← smt! seven = five
  let and_3 ← smt! ∧[equal_7_5_10, equal_5_10, seven_equal_five]
  let and_2 ← smt! equal_5_10 ∧ seven_equal_five
  show[and_3, and_2]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

and_3 ↦ (let ((_let_1 (= 7 5))) (let ((_let_2 (= 5 10))) (and (and _let_1 _let_2) _let_2 _let_1)))
and_2 ↦ (and (= 5 10) (= 7 5))
-/

[Term.or]
  let equal_7_5_10 ← smt! =[seven, five, ten]
  let equal_5_10 ← smt! five = ten
  let seven_equal_five ← smt! seven = five
  let or_3 ← smt! ∨[equal_7_5_10, equal_5_10, seven_equal_five]
  let or_2 ← smt! equal_5_10 ∨ seven_equal_five
  show[or_3, or_2]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

or_3 ↦ (let ((_let_1 (= 7 5))) (let ((_let_2 (= 5 10))) (or (and _let_1 _let_2) _let_2 _let_1)))
or_2 ↦ (or (= 5 10) (= 7 5))
-/

[Term.xor]
  let equal_7_5_10 ← smt! =[seven, five, ten]
  let equal_5_10 ← smt! five = ten
  let seven_equal_five ← smt! seven = five
  let xor_3 ← smt! ∨![equal_7_5_10, equal_5_10, seven_equal_five]
  let xor_2 ← smt! equal_5_10 ∨! seven_equal_five
  show[xor_3, xor_2]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

xor_3 ↦ (let ((_let_1 (= 7 5))) (let ((_let_2 (= 5 10))) (xor (xor (and _let_1 _let_2) _let_2) _let_1)))
xor_2 ↦ (xor (= 5 10) (= 7 5))
-/

[Term.implies]
  let equal_7_5_10 ← smt! =[seven, five, ten]
  let equal_5_10 ← smt! five = ten
  let seven_equal_five ← smt! seven = five
  let implies_3 ← smt! →[equal_7_5_10, equal_5_10, seven_equal_five]
  let implies_2 ← smt! equal_5_10 → seven_equal_five
  show[implies_3, implies_2]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

implies_3 ↦ (let ((_let_1 (= 7 5))) (let ((_let_2 (= 5 10))) (=> (and _let_1 _let_2) (=> _let_2 _let_1))))
implies_2 ↦ (=> (= 5 10) (= 7 5))
-/

[Term.distinct]
  let distinct_7_5_10 ← smt! ≠[seven, five, ten]
  let distinct_5_10 ← smt! five ≠ ten
  let seven_distinct_five ← smt! seven ≠ five
  show[distinct_7_5_10, distinct_5_10, seven_distinct_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

distinct_7_5_10 ↦ (distinct 7 5 10)
distinct_5_10 ↦ (distinct 5 10)
seven_distinct_five ↦ (distinct 7 5)
-/

[Term.lt]
  let lt_7_5_10 ← smt! <[seven, five, ten]
  let lt_5_10 ← smt! <[five, ten]
  let seven_lt_five ← smt! seven < five
  show[lt_7_5_10, lt_5_10, seven_lt_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

lt_7_5_10 ↦ (and (< 7 5) (< 5 10))
lt_5_10 ↦ (< 5 10)
seven_lt_five ↦ (< 7 5)
-/

[Term.le]
  let le_7_5_10 ← smt! ≤[seven, five, ten]
  let le_5_10 ← smt! ≤[five, ten]
  let seven_le_five ← smt! seven ≤ five
  show[le_7_5_10, le_5_10, seven_le_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

le_7_5_10 ↦ (and (<= 7 5) (<= 5 10))
le_5_10 ↦ (<= 5 10)
seven_le_five ↦ (<= 7 5)
-/

[Term.ge]
  let ge_7_5_10 ← smt! ≥[seven, five, ten]
  let ge_5_10 ← smt! ≥[five, ten]
  let seven_ge_five ← smt! seven ≥ five
  show[ge_7_5_10, ge_5_10, seven_ge_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

ge_7_5_10 ↦ (and (>= 7 5) (>= 5 10))
ge_5_10 ↦ (>= 5 10)
seven_ge_five ↦ (>= 7 5)
-/

[Term.gt]
  let gt_7_5_10 ← smt! >[seven, five, ten]
  let gt_5_10 ← smt! >[five, ten]
  let seven_gt_five ← smt! seven > five
  show[gt_7_5_10, gt_5_10, seven_gt_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

gt_7_5_10 ↦ (and (> 7 5) (> 5 10))
gt_5_10 ↦ (> 5 10)
seven_gt_five ↦ (> 7 5)
-/

[Term.add]
  let add_7_5_10 ← smt! +[seven, five, ten]
  let seven_add_five ← smt! seven + five
  show[add_7_5_10, seven_add_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

add_7_5_10 ↦ (+ 7 5 10)
seven_add_five ↦ (+ 7 5)
-/

[Term.mul]
  let mul_7_5_10 ← smt! *[seven, five, ten]
  let seven_mul_five ← smt! seven * five
  show[mul_7_5_10, seven_mul_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

mul_7_5_10 ↦ (* 7 5 10)
seven_mul_five ↦ (* 7 5)
-/

[Term.div!]
  let div_7_5_10 ← smt! /![seven, five, ten]
  let seven_div_five ← smt! seven /! five
  show[div_7_5_10, seven_div_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

div_7_5_10 ↦ (div (div 7 5) 10)
seven_div_five ↦ (div 7 5)
-/

[Term.divTotal]
  let div_5_10 ← smt! five / ten
  let seven_div_five ← smt! seven / five
  show[div_5_10, seven_div_five]
/-- info: boo ↦ false, not_boo ↦ (not false), seven ↦ 7, five ↦ 5, ten ↦ 10

div_5_10 ↦ (div_total 5 10)
seven_div_five ↦ (div_total 7 5)
-/
