/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Tactic.Init



namespace Cvc.Tactic.Test



/-- info: goal is **not** falsifiable ✅ -/
#test
example : ∀ (n1 n2 n3 n4 : Int),
  0 ≤ n1 → 0 ≤ n2 → n1 + 2*n2 - 3*n3 + 4*n4 = (n1 + 2*n2) - (3*n3 - 4*n4)
:= by
  falsifiable?
  omega

/--
warning: goal seems falsifiable, **it might not be provable**
---
warning: declaration uses 'sorry'
-/
#test
example : 1 = 2 := by
  falsifiable?
  sorry

/-- info: goal is **not** falsifiable ✅ -/
#test
example : 1 = 1 := by
  falsifiable?
  simp

/--
warning: goal seems falsifiable, **it might not be provable**
- n = 0
---
warning: declaration uses 'sorry'
-/
#test
example (n m : Int) : n % 3 = m → ∃ (k : Int), n = m + 3 * k := by
  falsifiable?
  sorry

/-- info:
(declare-sort Empty 0)
(define-fun nsub ((x Int) (y Int)) Int (ite (>= x y) (- x y) 0))
(define-fun itdiv ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (div x y) (- (div (- x) y)))))
(define-fun itmod ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (mod x y) (- (mod (- x) y)))))
(define-fun iediv ((x Int) (y Int)) Int (ite (= y 0) 0 (div x y)))
(define-fun iemod ((x Int) (y Int)) Int (ite (= y 0) x (mod x y)))
(declare-fun _n.186_ () Int)
(declare-fun _HMod.hMod (Int Int) Int)
(assert (! (not (exists ((_i Int)) (= _n.186_ (+ (_HMod.hMod _n.186_ 3) (* 3 _i))))) :named valid_fact_0))
(check-sat)
; sat
---
warning: goal seems falsifiable, **it might not be provable**
- [_n.186_] n = 0
-/
#test
example : ∀ (n m : Int), n % 3 = m → ∃ (k : Int), n = m + 3 * k := by
  falsifiable? (verbose)
  intro n
  simp [Int.emod_def]
  exists (n / 3)
  simp

/--
info: (declare-sort Empty 0)
(define-fun nsub ((x Int) (y Int)) Int (ite (>= x y) (- x y) 0))
(define-fun itdiv ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (div x y) (- (div (- x) y)))))
(define-fun itmod ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (mod x y) (- (mod (- x) y)))))
(define-fun iediv ((x Int) (y Int)) Int (ite (= y 0) 0 (div x y)))
(define-fun iemod ((x Int) (y Int)) Int (ite (= y 0) x (mod x y)))
(declare-fun _n.274_ () Int)
(declare-fun _HDiv.hDiv (Int Int) Int)
(assert (! (not (exists ((_i Int)) (= _n.274_ (+ (- _n.274_ (* 3 (_HDiv.hDiv _n.274_ 3))) (* 3 _i))))) :named valid_fact_0))
(check-sat)
; unsat
---
info: goal is **not** falsifiable ✅
-/
#test
example : ∀ (n m : Int), n % 3 = m → ∃ (k : Int), n = m + 3 * k := by
  falsifiable? (verbose) [Int.emod_def]
  intro n
  simp [Int.emod_def]
  exists (n / 3)
  simp

/--
info: goal is **not** falsifiable ✅
---
info: goal is **not** falsifiable ✅
---
info: goal is **not** falsifiable ✅
---
warning: declaration uses 'sorry'
-/
#test
example : ∀ (n m : Int), n % 3 = m → ∃ (k : Int), n = m + 3 * k := by
  simp [HMod.hMod, Mod.mod, Int.emod]
  intro n
  cases n <;> simp [Int.subNatNat]
  case ofNat n =>
    falsifiable? -- (verbose)
    sorry
  · split
    · falsifiable? -- (verbose)
      sorry
    · falsifiable? -- (verbose)
      sorry

/-- error: failed to decide (un)satifiability -/
#test
example : ∀ (n m : Nat), n % 3 = m → ∃ (k : Nat), n = m + 3 * k := by
  falsifiable?
  intro n ; simp
  exists (n / 3)
  omega

/-- info: goal is **not** falsifiable ✅ -/
#test
example : ∀ (n m : Nat), n % 3 = m → ∃ (k : Nat), n = m + 3 * k := by
  falsifiable? [Nat.mod_def]
  intro n ; simp
  exists (n / 3)
  omega

def mod (n m : Nat) := n % m

/-- error: failed to decide (un)satifiability -/
#test
example : ∀ (n m : Nat), mod n 3 = m → ∃ (k : Nat), n = m + 3 * k := by
  falsifiable? [Nat.mod_def] -- (verbose := true)
  intro n ; simp [mod]
  exists (n / 3)
  omega

/-- info: goal is **not** falsifiable ✅ -/
#test
example : ∀ (n m : Nat), mod n 3 = m → ∃ (k : Nat), n = m + 3 * k := by
  falsifiable? [Nat.mod_def] u[mod] -- (verbose := true)
  intro n ; simp [mod]
  exists (n / 3)
  omega

/--
info:
(declare-sort Empty 0)
(define-fun nsub ((x Int) (y Int)) Int (ite (>= x y) (- x y) 0))
(define-fun itdiv ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (div x y) (- (div (- x) y)))))
(define-fun itmod ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (mod x y) (- (mod (- x) y)))))
(define-fun iediv ((x Int) (y Int)) Int (ite (= y 0) 0 (div x y)))
(define-fun iemod ((x Int) (y Int)) Int (ite (= y 0) x (mod x y)))
(declare-fun _n.749_ () Int)
(assert (>= _n.749_ 0))
(assert (! (not (exists ((_n Int)) (and (>= _n 0) (= _n.749_ (+ (nsub _n.749_ (* 3 (iediv _n.749_ 3))) (* 3 _n)))))) :named valid_fact_0))
(check-sat)
; unsat
---
info: goal is **not** falsifiable ✅
-/
#test
example : ∀ (n m : Nat), n % 3 = m → ∃ (k : Nat), n = m + 3 * k := by
  falsifiable? (verbose) [Nat.mod_def]
  intro n ; simp
  exists (n / 3)
  omega

/-- info:
(declare-sort Empty 0)
(define-fun nsub ((x Int) (y Int)) Int (ite (>= x y) (- x y) 0))
(define-fun itdiv ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (div x y) (- (div (- x) y)))))
(define-fun itmod ((x Int) (y Int)) Int (ite (= y 0) x (ite (>= x 0) (mod x y) (- (mod (- x) y)))))
(define-fun iediv ((x Int) (y Int)) Int (ite (= y 0) 0 (div x y)))
(define-fun iemod ((x Int) (y Int)) Int (ite (= y 0) x (mod x y)))
(declare-fun _n1_ () Int)
(assert (>= _n1_ 0))
(declare-fun _n2_ () Int)
(assert (>= _n2_ 0))
(declare-fun _n3_ () Int)
(assert (>= _n3_ 0))
(assert (! (<= (+ _n1_ _n2_) _n3_) :named valid_fact_0))
(assert (! (not (<= (+ (* 4 _n1_) (* 4 _n2_)) (* 4 _n3_))) :named valid_fact_1))
(check-sat)
; unsat
---
info: goal is **not** falsifiable ✅
-/
#test
example (n1 n2 n3 : Nat) (h : n1 + n2 ≤ n3) : 4*n1 + 4*n2 ≤ 4*n3 := by
  falsifiable? (verbose)
  rw [← Nat.left_distrib]
  exact Nat.mul_le_mul (Nat.le_refl 4) h
