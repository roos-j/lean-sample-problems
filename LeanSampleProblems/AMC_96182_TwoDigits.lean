import Mathlib

/- The difference between a two-digit number and the number obtained by reversing its digits
is 5 times the sum of the digits of either number.  What is the sum of the two digit number and its reverse?

(A) 44
(B) 55
(C) 77
(D) 99
(E) 110 -/
theorem algebra_96182 {a b : Fin 10} (ha : 0 < a) (h : (10 * (a : ℤ) + b) - (10 * b + a) = 5 * (a + b)) :
    (10 * (a : ℤ) + b) + (10 * b + a) = 99 := by
  -- The assumption implies that the digits satisfy `2 * a = 7 * b`
  have h' : 2 * (a : ℤ) = 7 * b := by linarith only [h]
  -- Since this means that `a` is divisible by `7`, we must have `a = 7`
  have a_eq : a = 7 := by
    have amul : 7 ∣ (a : ℤ) := by
      have : 7 ∣ 2 * (a : ℤ) := by simp [h']
      exact Int.dvd_of_dvd_mul_right_of_gcd_one this rfl
    fin_cases a <;> norm_cast at amul
  rw [a_eq] at h'
  -- This implies in turn that `b = 2`, which gives the claim
  have b_eq : b = 2 := by fin_cases b <;> norm_cast at h'
  rw [a_eq, b_eq]
  norm_cast
