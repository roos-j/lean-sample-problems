import Mathlib

open Complex Finset ComplexConjugate

/- Calculate explicitly the sum:

$$\sum_{k=0}^{n}\binom{n}{k} \cos k x.$$
 -/
theorem algebra_125101 (n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), Nat.choose n k * Real.cos (k * x) =
    2 ^ n * (Real.cos (x / 2)) ^ n * Real.cos (n * x / 2) := by
  -- We first record a basic fact (why is this not in Mathlib?)
  have conj_exp_mul_I (x : ℝ) : conj (exp (x * I)) = exp (-x * I) := by
    norm_cast
    apply Complex.ext
    · rw [conj_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_re]
      exact (Real.cos_neg _).symm
    · rw [conj_im, exp_ofReal_mul_I_im, exp_ofReal_mul_I_im]
      exact (Real.sin_neg _).symm
  -- We can write the left hand side as the real part of a complex number
  conv => enter [1, 2, k]; rw [← exp_ofReal_mul_I_re]
  simp_rw [← re_ofReal_mul, ← re_sum]
  push_cast
  -- By the binomial theorem we have:
  have e1 :  ∑ k ∈ range (n + 1), Nat.choose n k * exp (k * x * I) = (1 + exp (x * I)) ^ n := by
    rw [add_comm (1 : ℂ), add_pow]
    apply sum_congr (by rfl)
    intro k _
    rw [← exp_nat_mul]
    ring_nf
  -- By Euler's formula we also have
  have e2 : 1 + exp (x * I) = 2 * exp (x / 2 * I) * Real.cos (x / 2) := by
    rw [← exp_ofReal_mul_I_re, re_eq_add_conj]
    rw [conj_exp_mul_I]
    ring_nf; rw [← exp_add, ← exp_add]
    push_cast; ring_nf
    simp only [exp_zero]; ring
  -- Using both of these we obtain the claim
  rw [e1, e2, mul_pow, mul_re, mul_pow, mul_re, ← exp_nat_mul, ← mul_assoc (n : ℂ)]
  norm_cast; rw [exp_ofReal_mul_I_re]
  norm_cast; ring_nf
