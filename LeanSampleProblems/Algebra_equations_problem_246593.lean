import Mathlib

open Real


/- Determine all values of the positive real number $k$ for which the equation
$$
\frac{\log (k x)}{\log (x+1)}=2
$$
has exactly one solution. -/
theorem algebra_246593 (k : ℝ) (hk : k > 0) :
    (∃! x > 0, log (k * x) / log (x + 1) = 2) ↔ k = 4 := by
  -- We first show that the equation is equivalent to a quadratic equation
  have h1 {x : ℝ} (hx : 0 < x) : log (k * x) / log (x + 1) = 2 ↔ 1 * (x * x) + (-k + 2) * x + 1 = 0 := by
    have : 0 < log (x + 1) := by apply log_pos; linarith only [hx]
    -- This is by using multiplying on both sides by the denominator, using logarithm rules and using injectivitiy of log
    constructor
    · intro h
      field_simp at h
      rw [← log_rpow (by positivity)] at h
      norm_cast at h
      have := log_injOn_pos (by simp; positivity) (by simp; positivity) h
      calc
        _ = x ^ 2 - (k * x) + 2 * x + 1 := by ring
        _ = _ := by rw [this]; ring
    · intro h
      field_simp
      rw [← log_rpow (by positivity)]
      norm_cast
      have : k * x = (x + 1) ^ 2 := by
        rw [← add_zero (k * x), ← h]; ring
      rw [this]

  -- Let `d` denote the discriminant of this quadratic equation
  let d := discrim 1 (-k + 2) 1
  -- If `d = 0`, then `k = 4`
  have k_eq_of_d_eq (hd : d = 0) : k = 4:= by
    by_cases hk' : 0 ≤ k - 2
    · -- If `0 ≤ k - 2`, then we can take square roots to show `k = 4` - uses that `k` is positive
      suffices k - 2 = 2 by linarith only [this]
      apply sq_eq_sq₀ (by positivity) (by norm_num) |>.mp
      simp [d, discrim] at hd; linarith only [hd]
    · -- If `k - 2 < 0`, then `k = 0` which is not allowed
      suffices 2 - k = 2 by linarith only [this, hk]
      apply sq_eq_sq₀ (by linarith only [hk']) (by norm_num) |>.mp
      simp [d, discrim] at hd; linarith only [hd]

  -- If the discriminant is negative, then `k` is larger than `4` - uses that `k` is positive
  have k_gt_of_d_gt (hd : 0 < d): 4 < k := by
    by_cases hk' : 0 ≤ k - 2
    · suffices 2 < k - 2 by linarith only [this]
      apply sq_lt_sq₀ (by norm_num) (by linarith only [hk']) |>.mp
      simp [d, discrim] at hd; linarith only [hd]
    · suffices 2 < 2 - k by linarith only [this, hk]
      apply sq_lt_sq₀ (by norm_num) (by linarith only [hk']) |>.mp
      simp [d, discrim] at hd; linarith only [hd]

  -- Since a quadratic equation has a unique solution iff its discriminant is zero, we get the claim
  constructor
  · -- First suppose there is a unique positive solution `x`
    intro h
    obtain ⟨x, ⟨hx, hx_sol⟩, hx_unique⟩ := h
    by_contra hk_ne -- Suppose `k ≠ 4`
    push_neg at hk_ne
    -- Distinguish the three cases whether discriminant is negative, zero or positive
    obtain h'|h'|h' := lt_trichotomy d 0
    · -- Discriminant can't be negative because there is a solution
      have d_ne_sq : ∀ s, d ≠ s ^ 2 := fun s ↦ by linarith only [h', sq_nonneg s]
      exact quadratic_ne_zero_of_discrim_ne_sq d_ne_sq x <| h1 hx |>.mp hx_sol
    · -- Discriminant is not zero because `k ≠ 4`
      exact hk_ne <| k_eq_of_d_eq h'
    · -- If discriminant would be positive there would be two solutions
      -- Subtlety: we need to show that these two solutions would both be positive; this uses `0 < k`
      have k_gt : 4 < k := k_gt_of_d_gt h'
      set xm := (-(-k + 2) - √d) / (2 * 1) with xm_def
      set xp := (-(-k + 2) + √d) / (2 * 1) with xp_def
      have sqrt_d_lt : √d < k - 2 := by
        convert sqrt_lt_sqrt (by positivity) (show d < (k - 2) ^ 2 by simp only [d, discrim]; linarith only) using 1
        exact sqrt_sq (by linarith only [k_gt]) |>.symm
      have xm_pos : 0 < xm := by simp only [xm]; linarith only [sqrt_d_lt]
      have xm_lt_xp : xm < xp := by simp only [xm, xp]; linarith [show 0 < √d by positivity]
      have xp_pos : 0 < xp := Trans.trans xm_pos xm_lt_xp
      have quad_sol := quadratic_eq_zero_iff (by norm_num) (show d = √d * √d by rw [← pow_two, sq_sqrt (by positivity)])
      rw [← xm_def, ← xp_def] at quad_sol
      obtain hx_xp|hx_xm := quad_sol x|>.mp <|h1 hx|>.mp hx_sol
      · -- Suppose `x = xp`. Then we can show `x = xm`, contradiction because `xp ≠ xm`
        suffices x = xm by linarith only [this, xm_lt_xp, hx_xp]
        refine hx_unique xm ?_ |>.symm
        constructor
        · exact xm_pos
        · apply h1 xm_pos |>.mpr
          apply quad_sol xm |>.mpr
          right; rfl
      · -- Same for the case `x = xm`
        suffices x = xp by linarith
        refine hx_unique xp ?_ |>.symm
        constructor
        · exact xp_pos
        · apply h1 xp_pos |>.mpr
          apply quad_sol xp |>.mpr
          left; rfl
  · -- Show that `k = 4` works
    intro hk
    use 1 -- `x = 1`
    and_intros
    · norm_num
    · rw [hk, mul_one, show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      norm_num
    · -- Show that solution is unique
      rintro y ⟨hy, hy_sol⟩
      have := h1 hy |>.mp hy_sol
      have := quadratic_eq_zero_iff (by norm_num) (show d = 0 * 0 by simp only [d, discrim, hk]; norm_num) y |>.mp this
      rw [hk] at this
      norm_num at this
      exact this
