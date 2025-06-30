import Mathlib

open Complex

/- The complex numbers $z$ and $w$ satisfy the system
$$z + 20i/w = 5 + i$$
$$w + 12i/z = −4 + 10i$$

Find the smallest possible value of $∣z w∣^2$. -/
theorem algebra_95383 (S : Set (ℂ × ℂ)) (f : ℂ × ℂ → ℝ) (hS : S = { (z ,w) | z * w ≠ 0 ∧ z + 20 * I / w = 5 + I ∧ w + 12 * I / z = -4 + 10 * I})
    (hf : f = fun (z, w) ↦ normSq (z * w)) : IsLeast (f '' S) 40 := by
  -- We begin by observing that `z * w` must satisfy a quadratic equation
  have hzw (z w : ℂ) : (z, w) ∈ S → 1 * ((z * w) * (z * w)) + (30 - 14 * I) * (z * w) + (-240) = 0 := by
    intro h
    rw [hS] at h
    obtain ⟨zw_ne_zero, e₁, e₂⟩ := h
    have : z ≠ 0 := left_ne_zero_of_mul zw_ne_zero
    have : w ≠ 0 := right_ne_zero_of_mul zw_ne_zero
    -- Multiplying the two equations gives:
    have : z * w + 32 * I - 240 / (z * w) = -30 + 46 * I := by
      calc
        _ = (z + 20 * I / w) * (w + 12 * I / z) := by field_simp; ring_nf; rw [I_sq]; ring
        _ = _ := by rw [e₁, e₂]; ring_nf; rw [I_sq]; ring
    -- Multiplying by `z * w` gives a quadratic equation in `z * w`
    calc
      _ = (z * w) * ((z * w + 32 * I - 240 / (z * w)) + 30 - 46 * I) := by set u := z * w; field_simp; ring
      _ = _ := by rw [this]; ring
  -- Thus by the quadratic formula we obtain that `z * w` can only be one of two values
  set u₁ : ℂ := 6 + I * 2 with u₁_def
  set u₂ : ℂ := -36 + I * 12 with u₂_def
  have zw_eq (z w : ℂ) : (z, w) ∈ S → z * w = u₁ ∨ z * w = u₂ := by
    intro h
    specialize hzw z w h
    set s := 42 - 10 * I with s_def
    have : discrim 1 (30 - 14 * I) (-240) = (42 - 10 * I) * (42 - 10 * I) := by
      rw [discrim]; ring_nf; rw [I_sq]; ring
    have := (quadratic_eq_zero_iff (by norm_num) this (z * w)).mp hzw
    ring_nf at this
    exact this
  -- Computing `|⬝|^2` of those two values shows that the smaller one is 40 as claimed
  have : normSq u₁ = 6 ^ 2 + 2 ^ 2 := by rw [u₁_def, normSq_apply]; norm_num
  have : normSq u₂ = 36 ^ 2 + 12 ^ 2 := by rw [u₂_def, normSq_apply]; norm_num
  -- Plugging in this value of `zw` also shows that `40` is attained for `z = 1 - I` and `w = 2 + 4 I`
  constructor
  · use (1 - I, 2 + 4 * I)
    have : 2 + 4 * I ≠ 0 := by by_contra h; have h := normSq_eq_zero.mpr h; rw [normSq_apply] at h; norm_num at h
    have : 1 - I ≠ 0 := by by_contra h; have h := normSq_eq_zero.mpr h; rw [normSq_apply] at h; norm_num at h
    constructor
    · rw [hS]; constructor
      · by_contra h; have h := normSq_eq_zero.mpr h; rw [normSq_apply] at h; norm_num at h
      · constructor <;> { field_simp; ring_nf; rw [I_sq]; ring }
    · rw [hf]; simp [normSq_apply]; norm_num
  · rintro x ⟨⟨z, w⟩, hzwS, hzwf⟩
    rw [← hzwf, hf]; dsimp
    obtain h|h := zw_eq z w hzwS
    · rw [h, u₁_def, normSq_apply]; norm_num
    · rw [h, u₂_def, normSq_apply]; norm_num
