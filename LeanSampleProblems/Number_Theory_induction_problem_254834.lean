import Mathlib

open Real

/- Prove: any positive integer power of $\sqrt{2}-1$
has the form $\sqrt{m}-\sqrt{m-1}$, where $m$ is some positive integer
(for example, $(\sqrt{2}-1)^{2}=\sqrt{9}-\sqrt{8}$). -/
theorem number_theory_254834 {n : ℕ} (hn : n > 0) :
    ∃ m : ℕ, m > 0 ∧ (√2 - 1)^n = √m - √(m - 1) := by
  -- It suffices to prove the following stronger statement by induction:
  suffices h : (Odd n → ∃ a b : ℕ, (√2 - 1) ^ n = a * √2 - b ∧ 2 * a ^ 2 = b ^ 2 + 1) ∧
      (Even n → ∃ a b : ℕ, (√2 - 1) ^ n = a - b * √2 ∧ a ^ 2 = 2 * b ^ 2 + 1) by
    by_cases hn' : Odd n
    · obtain ⟨a, b, ⟨hab, hab'⟩⟩ := h.1 hn'
      use 2 * a ^ 2
      have : a ≠ 0 := by
        by_contra!
        rw [this] at hab'
        simp at hab'
      constructor
      · positivity
      · rw [hab]
        nth_rewrite 2 [hab']
        push_cast
        rw [mul_comm]
        simp
    · simp only [Nat.not_odd_iff_even] at hn'
      obtain ⟨a, b, ⟨hab, hab'⟩⟩ := h.2 hn'
      use a ^ 2
      have : a ≠ 0 := by
        by_contra!
        rw [this] at hab'
        simp at hab'
      constructor
      · positivity
      · rw [hab]
        nth_rewrite 2 [hab']
        push_cast
        rw [mul_comm]
        simp
  -- We proceed by induction on `n`.
  induction' n with n ih
  · contradiction -- Claim holds vacuously for `n = 0`
  · -- Suppose claim holds for `n`. We need to show it holds for `n + 1`
    by_cases hnz : n = 0
    · -- Suppose `n + 1 = 1`; then we can use `a = b = 1`.
      rw [hnz]
      simp
      use 1, 1
      simp
    · have pos : 0 < n := by positivity
      by_cases hno : Odd n
      · -- Suppose `n` is odd. Then from the inductive hypothesis:
        obtain ⟨a, b, ⟨hab, hab'⟩⟩ := (ih pos).1 hno
        simp [hno]
        -- From the inductive hypothesis, the claim is true with the new `a, b` as follows:
        use 2 * a + b, a + b
        constructor
        · rw [pow_succ, hab]
          push_cast
          nlinarith only [sq_sqrt (show 0 ≤ 2 by norm_num)]
        · nlinarith only [hab']
      · -- Suppose `n` is even. Then from the inductive hypothesis:
        simp only [Nat.not_odd_iff_even] at hno
        obtain ⟨a, b, ⟨hab, hab'⟩⟩ := (ih pos).2 hno
        simp [hno]
        -- From the inductive hypothesis, the claim is true with the new `a, b` as follows:
        use a + b, a + 2 * b
        constructor
        · rw [pow_succ, hab]
          push_cast
          nlinarith only [sq_sqrt (show 0 ≤ 2 by norm_num)]
        · nlinarith only [hab']
