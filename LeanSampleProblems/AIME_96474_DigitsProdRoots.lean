import Mathlib

open Real Finset

/- Find the last three digits of the product of the positive roots of $\sqrt{1995}x^{\log_{1995}x}=x^2$. -/
theorem algebra_96474 {S : Set ℝ} [Fintype S]
    (hS : S = { x | 0 < x ∧ √1995 * x ^ (logb 1995 x) = x ^ 2}) :
    ⌊(∏ x ∈ S, x)⌋₊ % 1000 = 25 := by
  -- We will show that this equation has 2 positive roots as follows:
  set r₁ : ℝ := 1995 ^ (1 + √2/2) with r₁_def
  set r₂ : ℝ := 1995 ^ (1 - √2/2) with r₂_def
  have r₁_ne_r₂ : r₁ ≠ r₂ := by
    by_contra h
    have : 1 + √2/2 = 1 - √2/2 := by
      calc _ = logb 1995 (1995 ^ (1 + √2/2)) := by rw [logb_rpow (by positivity) (by norm_num)]
           _ = logb 1995 (1995 ^ (1 - √2/2)) := by rw [← r₁_def, h, r₂_def]
           _ = 1 - √2/2 := by rw [logb_rpow (by positivity) (by norm_num)]
    have s : √2/2 = - √2/2 := by linarith only [this]
    have : 0 < √2/2 := by positivity
    have : ¬ 0 < √2/2 := by rw [s]; apply not_lt.mpr; rw [neg_div]; exact neg_le.mp (show -0 ≤ √2/2 by rw [neg_zero]; positivity)
    contradiction
  -- The product `r₁ * r₂` is `1995^2`
  have r₁_mul_r₂ : r₁ * r₂ = 1995 ^ 2 := by
    rw [r₁_def, r₂_def, ← rpow_add (by positivity)]; simp; norm_cast
  -- This would imply the claim because `1995^2 % 1000 = 25`
  suffices h : S = {r₁, r₂} by
    simp_rw [h]
    rw [Set.toFinset_insert, prod_insert (by simp [r₁_ne_r₂]), Set.toFinset_singleton, prod_singleton]
    rw [r₁_mul_r₂]
    norm_cast; rw [Nat.floor_natCast]; norm_num
  -- Since these are solutions, it suffices to show there are no other solutions
  suffices h' : ∀ x, x ∈ S → x = r₁ ∨ x = r₂ by
    ext x
    refine ⟨h' x, ?_⟩
    rintro (hr | hr)
    · simp [hS, hr, r₁_def]
      refine ⟨by positivity, ?_⟩
      rw [← rpow_mul (by positivity), pow_two]
      rw [← pow_two, add_sq, one_pow, mul_one, pow_two, mul_div, mul_comm 2, ← mul_div, div_self (by norm_num), mul_one, ← rpow_add (by positivity)]
      rw [sqrt_eq_rpow, ← rpow_add (by norm_num)]
      rw [mul_div, ← mul_div_right_comm, mul_self_sqrt (by norm_num)]
      have : 1 / 2 + (1 + √2 + 2 / 2 / 2) = 1 + √2 / 2 + (1 + √2 / 2) := by linarith only
      rw [this]
    · simp only [Set.mem_singleton_iff] at hr
      simp [hS, hr, r₂_def]
      refine ⟨by positivity, ?_⟩
      rw [← rpow_mul (by positivity), pow_two]
      rw [← pow_two, sub_sq, one_pow, mul_one, pow_two, mul_div, mul_comm 2, ← mul_div, div_self (by norm_num), mul_one, ← rpow_add (by positivity)]
      rw [sqrt_eq_rpow, ← rpow_add (by norm_num)]
      rw [mul_div, ← mul_div_right_comm, mul_self_sqrt (by norm_num)]
      have : 1 / 2 + (1 - √2 + 2 / 2 / 2) = 1 - √2 / 2 + (1 - √2 / 2) := by linarith only
      rw [this]
  -- Let `x` be a solution
  intro x hx
  rw [hS] at hx
  obtain ⟨x_pos, hx⟩ := hx
  -- Applying logarithm base 1995 on both sides of the equation gives us a quadratic equation
  have hx2 : 2 * (logb 1995 x)^2 - 4 * (logb 1995 x) + 1 = 0 := by
    have : logb 1995 (√1995 * x ^ logb 1995 x) = logb 1995 (x ^ 2) := by rw [hx]
    rw [logb_mul (by norm_num) (ne_of_gt (by positivity)), sqrt_eq_rpow, logb_pow, logb_rpow (by positivity) (by norm_num),
      logb_rpow_eq_mul_logb_of_pos x_pos] at this
    linarith only [this]
  -- Thus we can compute the solutions by the quadratic formula
  have : logb 1995 x = 1 + √2/2 ∨ logb 1995 x = 1 - √2/2 := by
    have : discrim 2 (-4) 1 = √8 * √8 := by rw [discrim]; norm_num
    have := (quadratic_eq_zero_iff (by norm_num) this (logb 1995 x)).mp
    specialize this (by linarith only [hx2])
    have aux1 : √8 / 4 = √2 / 2 := by
      rw [show (8:ℝ) = 2^2 * 2 by norm_num, sqrt_mul (by positivity), sqrt_sq (by positivity), mul_comm, mul_div_assoc]
      rw [show (2:ℝ)/4 = 1/2 by norm_num, ← mul_div_assoc, mul_one]
    norm_cast at this; simp [add_div, sub_div, aux1] at this
    exact this
  obtain h|h := this
  · left; rw [r₁_def]
    rw [← logb_rpow (show 0 < 1995 by positivity) (by norm_num) (x := 1 + √2/2)] at h
    exact logb_injOn_pos (by norm_num) x_pos (rpow_pos_of_pos (by positivity) _) h
  · right; rw [r₂_def]
    rw [← logb_rpow (show 0 < 1995 by positivity) (by norm_num) (x := 1 - √2/2)] at h
    exact logb_injOn_pos (by norm_num) x_pos (rpow_pos_of_pos (by positivity) _) h
