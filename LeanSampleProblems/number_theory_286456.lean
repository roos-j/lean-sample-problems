import Mathlib

open Int

/- Let $a$ be an integer that ends in 4 but is not a multiple of 4. Prove that

$$a\left(a^{2}-1\right)\left(a^{2}-4\right)$$

is a multiple of 960. -/
theorem number_theory_286456 (a : ℤ) (h₀ : a % 10 = 4) (h₁ : ¬(4 ∣ a)) :
    960 ∣ a * (a ^ 2 - 1) * (a ^ 2 - 4) := by
  set N := a * (a ^ 2 - 1) * (a ^ 2 - 4)
  -- We begin by factoring the expression in question:
  have N_eq : N = (a - 2) * (a - 1) * a * (a + 1) * (a + 2) := by ring
  -- Since `960 = 2 ^ 6 * 3 * 5` it suffices to show that `2 ^ 6`, `3` and `5` are divisors:
  suffices h : 2 ^ 6 ∣ N ∧ 3 ∣ N ∧ 5 ∣ N by omega
  and_intros
  · -- We need to show that `2 ^ 6` divides `N`
    apply dvd_of_emod_eq_zero
    -- `a` is even and not divisible by four, so `a - 2` and `a + 2` are both divisible by four
    have h1 : 2 ∣ a ∧ 4 ∣ (a - 2) ∧ 4 ∣ (a + 2) := by omega
    -- Thus, one of them must be divisible by `8`
    have h2 : 8 ∣ (a - 2) ∨ 8 ∣ (a + 2) := by omega
    -- Since `a, a - 2, a + 2` divide `N`, we found `1 + 2 + 3 = 6` factors of `2`
    obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := h1
    obtain ⟨k4, hk4⟩ | ⟨k4, hk4⟩ := h2
    · have h3 : N = 2 ^ 6 * (k4 * (a - 1) * (a + 1) * k1 * k3) := by
        rw [N_eq, hk3, hk4]
        nth_rewrite 2 [hk1]
        ring
      rw [h3]
      simp only [mul_emod_right]
    · have h3 : N = 2 ^ 6 * (k4 * (a - 1) * (a + 1) * k1 * k2) := by
        rw [N_eq, hk2, hk4]
        nth_rewrite 2 [hk1]
        ring
      rw [h3]
      simp only [mul_emod_right]
  · -- Since `N` is a product of five consecutive integers, it must be divisible by three
    apply dvd_of_emod_eq_zero
    have : a % 3 < 3 := emod_lt_of_pos _ (by norm_num)
    have : 0 ≤ a % 3 := emod_nonneg _ (by norm_num)
    rw [N_eq]
    rw [mul_emod, mul_emod _ (a + 1), mul_emod _ a, mul_emod _ (a - 1)]
    rw [sub_emod, sub_emod a 1, add_emod, add_emod a 2]
    interval_cases a % 3 <;> norm_num
  · -- Since `N` is a product of five consecutive integers, it must be divisible by five
    have : a % 5 < 5 := emod_lt_of_pos _ (by norm_num)
    have : 0 ≤ a % 5 := emod_nonneg _ (by norm_num)
    apply dvd_of_emod_eq_zero
    rw [N_eq]
    rw [mul_emod, mul_emod _ (a + 1), mul_emod _ a, mul_emod _ (a - 1)]
    rw [sub_emod, sub_emod a 1, add_emod, add_emod a 2]
    interval_cases a % 5 <;> norm_num
