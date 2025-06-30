import Mathlib

open Real

/- Find the positive integer $n$ such that

$$\arctan⁡\frac13+\arctan⁡\frac14+\arctan⁡\frac15+\arctan⁡\frac1{n}=\pi/4.$$

-/
theorem algebra_93841 (n : ℕ) (hn : 1 ≤ n) :
    arctan (1 / 3) + arctan (1 / 4) + arctan (1 / 5) + arctan (1 / n) = π / 4 ↔ n = 47 := by
  -- We first use the addition formula for `arctan` and the fact that `π / 4 = arctan 1`
  have aux₀ : (1 : ℝ) ≤ n := by norm_cast
  have aux₁ : 23 / 24 * (n : ℝ)⁻¹ < 1 := by
    calc _ < 1 * (n : ℝ)⁻¹ := by gcongr; norm_num
         _ ≤ 1 * 1 := by gcongr; field_simp; exact (div_le_one (by positivity)).mpr aux₀
         _ = 1 := mul_one _
  rw [arctan_add (by norm_num), arctan_add (by norm_num), arctan_add (by norm_num; linarith only [aux₁]), ← arctan_one]
  constructor
  · intro h
    -- Using that `arctan` is injective, we obtain a linear equation for `n`
    have e : (23 : ℝ) * n + 24 = 24 * n - 23 := by
      have h' := arctan_injective h
      norm_num at h'
      have : (24 : ℝ) * n - 23 ≠ 0 := by linarith only [aux₀]
      field_simp at h'
      exact h'
    -- Solving this linear equation gives `n = 47`
    have : (n : ℝ) = 47 := by linarith only [e]
    exact_mod_cast this
  · intro hn; rw [hn]; norm_num
