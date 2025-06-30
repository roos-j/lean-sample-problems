import Mathlib

/- Find the positive solution $x$ to

  $$1/(x^2 - 10x - 29) + 1/(x^2 - 10x - 45) - 2/(x^2 - 10x - 69) = 0.$$
 -/

theorem algebra_95672 (x : ℝ) (hx : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0) (h₂ : x ^ 2 - 10 * x - 45 ≠ 0)
  (h₃ : x ^ 2 - 10 * x - 69 ≠ 0) : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0 → x = 13 := by
  intro h
  -- We begin with a substitution
  set a := x ^ 2 - 10 * x - 29 with a_def
  have a_sub_eq (b : ℝ) : a - b = x^2 - 10 * x - (29 + b) := by ring_nf
  -- Then the equation becomes
  have s1 : 1 / a + 1 / (a - 16) - 2 / (a - 40) = 0 := by
    ring_nf at h; ring_nf; assumption
  -- Multiplying out denominators we get the following equation for `a`:
  have s2 : (a - 16) * (a - 40) + a * (a - 40) - 2 * a * (a - 16) = 0 := by
    have : a - 16 ≠ 0 := by rw [a_sub_eq]; norm_cast
    have : a - 40 ≠ 0 := by rw [a_sub_eq]; norm_cast
    calc
      _ = (1 / a + 1 / (a - 16) - 2 / (a - 40)) * (a * (a - 16) * (a - 40)) := by
        nth_rewrite 3 [sub_mul]
        rw [add_mul]
        field_simp
        ring_nf
      _ = 0 := by rw [s1, zero_mul]
  -- Factoring this out, the square cancels and we get a linear equation for `a`
  have s3 : -64 * a + 40 * 16 = 0 := by
    have {a : ℝ} : (a - 16) * (a - 40) + a * (a - 40) - 2 * a * (a - 16) = 0 → -64 * a + 40 * 16 = 0 := by
      intro ha
      ring_nf at ha
      ring_nf
      exact ha
    exact this s2
  -- Solving the linear equation gives `a = 10`
  have s4 : a = 10 := by linarith
  -- Substituting the definition of `a` and factoring the quadratic in `x` gives:
  have s5 : 0 = (x - 13) * (x + 3) := by linarith
  -- Since `x` is positive, we must have that `x = 13`
  cases zero_eq_mul.mp s5 <;> linarith
