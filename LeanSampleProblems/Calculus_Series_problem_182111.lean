import Mathlib

open Finset Real Nat intervalIntegral

/- Prove: $\sum_{k=1}^{\infty}(-1)^{k} C_{n}^{k}\left(1+\frac{1}{2}+\cdots+\frac{1}{k}\right)=-\frac{1}{n}$. -/
theorem algebra_182111 {n : ℕ} :
    ∑' k : ℕ, (-1 : ℝ)^k * Nat.choose n k * (∑ i in Icc 1 k, (1 : ℝ) / i) = -1 / n := by
  -- First note that this series is a finite sum, because the summand is `0` if `k > n`
  suffices h : ∑ k ∈ Icc 1 n, (-1 : ℝ)^k * Nat.choose n k * (∑ i in Icc 1 k, ((1 : ℝ) / i)) = -1 / n by {
    convert tsum_eq_sum (s := Icc 1 n) ?_
    · exact h.symm
    · intro k hk
      simp only [mem_Icc, not_and_or, not_le] at hk
      -- Either `k < 1` or `k > n`
      obtain hk|hk := hk
      · simp [hk]
      · simp [choose_eq_zero_of_lt hk]
  }
  -- Auxiliary lemma on binomial coefficients
  have choose_succ_left' {n k : ℕ} : (n + 1).choose k = if 0 < k then n.choose (k - 1) + n.choose k  else 1 := by
    split_ifs with h
    · exact choose_succ_left _ _ h
    · simp at h; simp [h]
  -- The idea is to use induction on `n`. To close the inductive step we will need the following simpler claim:
  have e1 : ∀ n : ℕ, ∑ k ∈ Icc 1 n, (-1) ^ (k + 1) * ↑(n.choose k) * 1 / ((k : ℝ) + 1) = 1 - 1 / (n + 1) := by
    intro n
    -- The idea is to integrate the binomial theorem; first write `1 / (k + 1)` as an integral:
    have h1 {k : ℕ} : 1 / ((k : ℝ) + 1) = ∫ x in (0 : ℝ)..1, x ^ k := by rw [integral_pow]; ring
    simp_rw [mul_div_assoc]
    conv => enter [1, 2, k]; rw [h1, mul_comm, ← integral_mul_const]
    rw [← integral_finset_sum]
    rotate_left; focus { intro i hi; apply ContinuousOn.intervalIntegrable; fun_prop }
    -- Then we interchange sum and integral and use the binomial theorem
    -- Then integrate `(1 - x)^n` by the fundamental theorem of calculus
    have h2 : deriv (fun x : ℝ ↦ -1 / (n + 1) * (1 - x) ^ (n + 1)) = fun x ↦ (1 - x) ^ n := by
      ext
      apply HasDerivAt.deriv
      convert HasDerivAt.const_mul (d := fun x : ℝ ↦ (1 - x) ^ (n + 1)) _ ?_
      rotate_right
      convert HasDerivAt.pow (n + 1) (HasDerivAt.const_sub _ (hasDerivAt_id _))
      field_simp
    calc
      _ = ∫ x in (0:ℝ)..1, ∑ k ∈ Icc 1 n, -((-x) ^ k * 1 ^ (n - k) * n.choose k) := by congr! 3; ring
      _ = ∫ x in (0:ℝ)..1, 1 - ∑ k ∈ range (n + 1), (-x) ^ k * 1 ^ (n - k) * n.choose k := by
        simp_rw [sum_range_eq_add_Ico _ (show 0 < n + 1 by positivity)]; simp; congr
      _ = ∫ x in (0:ℝ)..1, 1 - (1 - x) ^ n := by
        congr!; rw [← add_pow]; ring
      _ = 1 - ∫ x in (0:ℝ)..1, (1 - x) ^ n := by
        rw [integral_sub, integral_const]
        · simp
        · exact intervalIntegrable_const _
        · apply ContinuousOn.intervalIntegrable; fun_prop
      _ = _ := by
        congr
        convert integral_deriv_eq_sub (a := 0) (b := 1) (f := fun x ↦ -1 / (n + 1) * (1 - x) ^ (n + 1)) ?_ ?_ using 1
        · rw [h2]
        · ring
        · fun_prop
        · apply ContinuousOn.intervalIntegrable; rw [h2]; fun_prop
  -- We proceed by induction on `n`
  induction' n with n ih
  · simp -- For `n = 0` there is nothing to show
  · -- Suppose it holds for `n`, then we show it holds for `n + 1`
    wlog hn : 0 < n; focus simp [show n = 0 by omega]
    rw [sum_Icc_succ_top]
    simp_rw [choose_succ_left']
    rotate_left; omega
    push_cast
    simp only [mul_ite, ite_mul]; rw [sum_ite]
    rw [filter_true_of_mem (by intro _ hx; simp at hx; omega)]
    rw [filter_false_of_mem (by intro _ hx; simp at hx; omega)]
    rw [sum_empty, add_zero]
    simp_rw [mul_add, add_mul]
    rw [sum_add_distrib]
    rw [ih]
    simp [-one_div]
    have e3 : ∑ k ∈ Icc 1 n, (-1 : ℝ) ^ k * n.choose (k - 1) * ∑ j ∈ Icc 1 k, (1 : ℝ) / j =
        -1 -  (-1 : ℝ) ^ (n + 1) * ∑ j ∈ Icc 1 (n + 1), (1 : ℝ) / j + 1 / n
            + ∑ k ∈ Icc 1 n, (-1 : ℝ) ^ (k + 1) * n.choose k * 1 / (k + 1) := by
      calc
        _ = ∑ k ∈ range n, (-1 : ℝ) ^ (k + 1) * n.choose k * ∑ j ∈ Icc 1 (k + 1), (1 : ℝ) / j := by
          convert sum_bij (fun k hk ↦ k - 1) ?_ ?_ ?_ ?_
          · intro _ h; simp at h; simp; omega
          · intro _ h _ h'; simp at h; simp at h'; simp; omega
          · intro k hk; use k + 1, (by simp at hk; simp; omega); simp
          · intro k hk; simp at hk; simp [show k - 1 + 1 = k by omega]
        _ = -1 + ∑ k ∈ Ico 1 n, (-1 : ℝ) ^ (k + 1) * n.choose k * ∑ j ∈ Icc 1 (k + 1), (1 : ℝ) / j := by
          rw [sum_range_eq_add_Ico]
          · simp
          · exact hn
        _ = -1 -  (-1 : ℝ) ^ (n + 1) * ∑ j ∈ Icc 1 (n + 1), (1 : ℝ) / j
            + ∑ k ∈ Icc 1 n, (-1 : ℝ) ^ (k + 1) * n.choose k * ∑ j ∈ Icc 1 (k + 1), (1 : ℝ) / j := by
          simp [← sum_Ico_add_eq_sum_Icc (show 1 ≤ n by omega)]
        _ = -1 -  (-1 : ℝ) ^ (n + 1) * ∑ j ∈ Icc 1 (n + 1), (1 : ℝ) / j + 1 / n
            + ∑ k ∈ Icc 1 n, (-1 : ℝ) ^ (k + 1) * n.choose k * 1 / (k + 1) := by
          conv =>
            enter [1, 2, 2, k]
            rw [sum_Icc_succ_top (by omega)]
            rw [mul_add]
            enter [1]
            rw [pow_succ, mul_comm _ (-1), mul_assoc (-1) _ _, mul_assoc (-1) _ _, neg_mul, one_mul]
          rw [sum_add_distrib, sum_neg_distrib, ih]
          field_simp; ring
    rw [e3]
    calc
      _ = (-1 : ℝ) + ∑ k ∈ Icc 1 n, (-1) ^ (k + 1) * ↑(n.choose k) * 1 / ((k : ℝ) + 1) := by ring
      _ = _ := by rw [e1]; ring
