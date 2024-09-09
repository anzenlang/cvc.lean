import CvcTest.Tactic.Init



namespace Cvc.Tactic.Test



/-- info: goal is **not** falsifiable ✅ -/
#test
example : ∀ (n1 n2 n3 n4 : Int),
  0 ≤ n1 → 0 ≤ n2 → n1 + 2*n2 - 3*n3 + 4*n4 = (n1 + 2*n2) - (3*n3 - 4*n4)
:= by
  falsifiable?
  omega

/-- error: goal **is falsifiable** -/
#test
example : 1 = 2 := by
  falsifiable?
  sorry

/-- info: goal is **not** falsifiable ✅ -/
#test
example : 1 = 1 := by
  falsifiable?
  simp

/-- error: goal **is falsifiable** -/
#test
example : ∀ (n m : Int), n % 3 = m → ∃ (k : Int), n = m + 3 * k := by
  falsifiable?
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
(declare-fun _n.457_ () Int)
(assert (>= _n.457_ 0))
(assert (! (not (exists ((_n Int)) (and (>= _n 0) (= _n.457_ (+ (nsub _n.457_ (* 3 (iediv _n.457_ 3))) (* 3 _n)))))) :named valid_fact_0))
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
