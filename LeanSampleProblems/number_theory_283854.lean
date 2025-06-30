import Mathlib

/- Given that the sum of two positive integers is 432,
  the sum of the least common multiple and the greatest common divisor
  of these two positive integers is 7776. Then the product of these
  two positive integers is 46620. -/
theorem number_theory_283854 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hsum : x + y = 432) (hlcm : Nat.lcm x y + Nat.gcd x y = 7776) :
    x * y = 46620 := by
  -- Wlog. we may assume that `y ≤ x`
  wlog hxy : y ≤ x
  focus {
    push_neg at hxy
    rw [mul_comm]
    refine this hy hx ?_ ?_ ?_
    · rw [add_comm]; exact hsum
    · rw [Nat.lcm_comm, Nat.gcd_comm]; exact hlcm
    · apply le_of_lt; exact hxy
  }
  -- Let the greatest common divisor be `d` and let `n, m` be so that `x = d * m, y = d * n`
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := Nat.gcd_dvd x y
  set d := x.gcd y with d_def
  -- `d` is positive
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hx
  -- Then `m`, `n` are coprime
  have h0 : m.gcd n = 1 := by
    apply Nat.coprime_iff_gcd_eq_one.mp
    convert Nat.coprime_div_gcd_div_gcd (m := x) (n := y) hdpos
    · rw [← d_def, hm, mul_comm, Nat.mul_div_cancel m hdpos]
    · rw [← d_def, hn, mul_comm, Nat.mul_div_cancel n hdpos]
  -- Then the lcm is `d * m * n`
  have h1 : x.lcm y = d * m * n := by
    rw [hm, hn, Nat.lcm_mul_left, mul_assoc, ← m.gcd_mul_lcm n, h0, one_mul]
  -- Then from `hsum`
  have h2 : d * (m + n) = 432 := by
    rwa [hm, hn, ← mul_add] at hsum
  -- Then from `hlcm`:
  have h3 : d * (m * n + 1) = 7776 := by
    rwa [h1, mul_assoc] at hlcm
  -- This implies:
  have h4 : ((m * n + 1) : ℤ) = 18 * (m + n) := by
    norm_cast
    rw [show 7776 = 18 * 432 by rfl, ← h2, mul_comm 18 _, mul_assoc, mul_comm _ 18] at h3
    exact Nat.eq_of_mul_eq_mul_left hdpos h3
  -- Rearranging this:
  have h5 : (m * n : ℤ) - 18 * (m + n) + 1 = 0 := by
    linarith only [h4]
  -- Then:
  have h6 : ((m : ℤ) - 18) * (n - 18) = 17 * 19 := by
    linarith only [h5]
  -- Since `y ≤ x` we have `n ≤ m`
  have hnm : n ≤ m := by
    rw [hm, hn] at hxy
    exact le_of_mul_le_mul_left hxy hdpos
  -- Since `17` and `19` are prime, `h6` thus implies
  have h7 :  ((m : ℤ) - 18 = 17 * 19 ∧ (n : ℤ) - 18 = 1) ∨ ((m : ℤ) - 18 = 19 ∧ (n : ℤ) - 18 = 17) := by
    -- This is obvious to humans but unfortunately lengthy here
    set a := (m : ℤ) - 18 with a_def
    set b := (n : ℤ) - 18 with b_def
    have hab : b ≤ a := by rw [b_def, a_def]; linarith only [hnm]
    have hdvd : 19 ∣ a * b := by omega
    have h19p : Prime (19 : ℤ) := by norm_num
    have h17p : Prime (17 : ℤ) := by norm_num
    obtain ⟨k, hk⟩|⟨k, hk⟩ := h19p.dvd_or_dvd hdvd
    · have : k * b = 17 := by
        rw [hk, mul_assoc, mul_comm 17] at h6
        exact Int.eq_of_mul_eq_mul_left (by norm_num) h6
      obtain ⟨l, hl⟩|⟨l, hl⟩ := h17p.dvd_or_dvd (show 17 ∣ k * b by omega)
      · have : l * b = 1 := by
          rw [hl, mul_assoc] at this
          nth_rewrite 2 [← mul_one 17] at this
          exact Int.eq_of_mul_eq_mul_left (by norm_num) this
        have hb : b = 1 := by
          obtain h|h := Int.mul_eq_one_iff_eq_one_or_neg_one.mp this
          · exact h.2
          · omega
        have ha : a = 17 * 19 := by rwa [hb, mul_one] at h6
        left
        exact ⟨ha, hb⟩
      · have : k * l = 1 := by
          rw [hl, mul_comm 17, ← mul_assoc] at this
          nth_rewrite 2 [← one_mul 17] at this
          exact Int.eq_of_mul_eq_mul_right (by norm_num) this
        have : l = 1 := by
          obtain h|h := Int.mul_eq_one_iff_eq_one_or_neg_one.mp this
          · exact h.2
          · omega
        have hb : b = 17 := by rwa [this] at hl
        have ha : a = 19 := by
          rw [hb, mul_comm a] at h6
          exact Int.eq_of_mul_eq_mul_left (by norm_num) h6
        right
        exact ⟨ha, hb⟩
    · -- `b` can't be divisible by `19` because `b ≤ a`
      have : a * k = 17 := by
        rw [hk, mul_comm 19, ← mul_assoc] at h6
        exact Int.eq_of_mul_eq_mul_right (by norm_num) h6
      obtain ⟨l, hl⟩|⟨l, hl⟩ := h17p.dvd_or_dvd (show 17 ∣ a * k by omega)
      · have : l * k = 1 := by
          rw [hl, mul_assoc] at this
          nth_rewrite 2 [← mul_one 17] at this
          exact Int.eq_of_mul_eq_mul_left (by norm_num) this
        have : l = 1 := by
          obtain h|h := Int.mul_eq_one_iff_eq_one_or_neg_one.mp this
          · exact h.1
          · omega
        rw [this] at hl
        rw [hl] at h6
        omega -- Contradiction
      · have : a * l = 1 := by
          rw [hl, mul_comm 17, ← mul_assoc] at this
          nth_rewrite 2 [← one_mul 17] at this
          exact Int.eq_of_mul_eq_mul_right (by norm_num) this
        have : a = 1 := by
          obtain h|h := Int.mul_eq_one_iff_eq_one_or_neg_one.mp this
          · exact h.1
          · omega
        rw [this, one_mul] at h6
        omega -- Contradiction
  -- We distinguish the two cases:
  obtain h7 | h7 := h7
  · -- In the first case we get `m + n = 360` which is not possible
    have hmn : m + n = 360 := by omega
    -- But this is a contradiction to `h2`
    rw [hmn] at h2
    omega
  · -- In the second case, `m = 37, n = 35`.
    have hm' : m = 37 := by omega
    have hn' : n = 35 := by omega
    -- From `h2` we then get the value of `d`:
    have hd : d = 6 := by
      rw [hm', hn'] at h2
      omega
    rw [hm, hn, hm', hn', hd]
