import Mathlib

namespace inequalities_105387

open Real Finset

/- Auxiliary lemma: if `sin x ≠ 0`, then the same is true for `x / 2 ^ k` -/
lemma l_sin_nz_aux {x : ℝ} (hx : sin x ≠ 0) (k : ℕ) : sin (x / 2 ^ k) ≠ 0 := by
  by_contra h
  apply hx
  apply sin_eq_zero_iff.mpr
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h
  use 2 ^ k * n
  field_simp at hn
  push_cast
  linarith only [hn]

/- Missing trig identity -/
lemma cot_sub {x y : ℝ} (hx : sin x ≠ 0) (hy : sin y ≠ 0) : cot x - cot y = sin (y - x) / (sin x * sin y) := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_sub]
  field_simp
  ring

/- The variant we need below -/
lemma cot_div_two_sub_cot {x : ℝ} (hx : sin x ≠ 0) : cot (x / 2) - cot x = 1 / sin x := by
  have := l_sin_nz_aux hx 1
  rw [pow_one] at this
  have := cot_sub this hx
  rw [show x - x / 2 = x / 2 by linarith only] at this
  rw [show sin (x / 2) / (sin (x / 2) * sin x) = 1 / sin x by field_simp] at this
  assumption

/-
Prove: If $0 < x < \pi$, $n$ is a natural number, then

$$\cot \frac{x}{2^{n}}-\cot x \geqslant n$$

-/
theorem inequalities_105387 (x : ℝ) (hx : 0 < x ∧ x < π) (n : ℕ) :
    cot (x / (2 ^ n)) - cot x ≥ n := by
  -- We first note that by assumption, `sin x ≠ 0`
  have hx' : sin x ≠ 0 := ne_of_gt <| sin_pos_of_mem_Ioo hx
  -- Add and substract terms `cot (x / 2 ^ i)` to rewrite the left hand side as a telescoping sum
  calc
    _ = ∑ k in range n, (cot (x / 2 ^ (k + 1)) - cot (x / 2 ^ k)) := by
      rw [sum_range_sub (f := fun k ↦ cot (x / 2 ^ k))]
      simp
    -- Then use the trignometric identity
    _ = ∑ k in range n, 1 / sin (x / 2 ^ k) := by
      congr! 1 with k
      convert cot_div_two_sub_cot <| l_sin_nz_aux hx' k using 3
      field_simp [pow_succ]
    _ ≥ ∑ k in range n, 1 := by
      gcongr with k
      have : 0 < sin (x / 2 ^k) := by
        apply sin_pos_of_mem_Ioo
        constructor
        · have := hx.1; positivity
        · refine lt_of_mul_lt_mul_left ?_ (show 0 ≤ 2 ^ k by positivity)
          field_simp
          calc
            _ < π := hx.2
            _ = 1 * π := (one_mul _).symm
            _ ≤ _ := by
              gcongr
              norm_cast
              exact Nat.one_le_two_pow
      refine le_of_mul_le_mul_left ?_ this
      field_simp [sin_le_one]
    _ = _ := by
      simp

end inequalities_105387
