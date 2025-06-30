import Mathlib

open Real Finset Filter

/- Evaluate $\sum_{k=0}^{\infty} \frac{2}{\pi} \tan ^{-1}\left(\frac{2}{(2 k+1)^{2}}\right)$. -/
theorem calculus_287040 : ∑' k : ℕ, 2 / π * arctan (2 / (2 * k + 1) ^ 2) = 1 := by
  -- We first rewrite the summand to expose a telescoping sum from the second summand on
  have h {k : ℕ} (hk : 0 < k) : arctan (2 / (2 * k + 1) ^ 2) = arctan (1 / (2 * k)) - arctan (1 / (2 * k + 2)) := by
    -- We use the addition formula for `arctan`
    rw [sub_eq_add_neg, ← arctan_neg, arctan_add]
    · congr! 1
      norm_cast
      field_simp
      ring
    · calc
        _ < (0 : ℝ) := by
          simp only [one_div, mul_inv_rev, mul_neg, Left.neg_neg_iff]
          positivity
        _ ≤ _ := by positivity
  -- `arctan` of a nonnegative argument is nonnegative
  have arctan_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ arctan x := by
    convert arctan_strictMono.monotone hx
    exact arctan_zero.symm
  have haux : ∀ k : ℕ, 0 ≤ 2 / π * arctan (2 / (2 * ↑k + 1) ^ 2) := by
    intro k
    have := arctan_nonneg (show 0 ≤ (2 : ℝ) / (2 * k + 1) ^ 2 by positivity)
    positivity
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg haux]
  -- Unfortunately we need to show this by passing through first principles:
  rw [Metric.tendsto_atTop]
  intro ε hε -- Let `ε > 0`
  -- We will reduce the claim to the following auxiliary limit:
  have htendsto_aux : Tendsto (fun n : ℕ ↦ ((π - 2 * arctan (1 / (2 * n))) / π)) atTop (nhds 1) := by
    -- This follows from continuity of `arctan` at `0`
    have arctan_tendsto_zero : Tendsto arctan (nhds 0) (nhds 0) := by
      have := continuousAt_arctan (x := 0)
      rw [ContinuousAt, arctan_zero] at this
      assumption
    have haux : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 * n)) atTop (nhds 0) := by
      apply Tendsto.const_div_atTop
      rw [tendsto_atTop_atTop]
      intro N
      use ⌈N⌉₊
      intro n hn
      calc
        _ ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ 2 * ⌈N⌉₊ := by linarith only
        _ ≤ _ := by gcongr
    have haux' : Tendsto (fun n : ℕ ↦ arctan (1 / (2 * n))) atTop (nhds 0) := by
      set f : ℕ → ℝ := fun n ↦ 1 / (2 * n) with f_def
      have hcomp {n : ℕ} :  arctan (1 / (2 * n)) = (arctan ∘ f) n := by rfl
      simp_rw [hcomp]
      apply Tendsto.comp (y := nhds 0)
      · exact arctan_tendsto_zero
      · exact haux
    convert Tendsto.div_const (Tendsto.const_sub π (Tendsto.const_mul (2 : ℝ) <| haux')) π using 2
    field_simp
  rw [Metric.tendsto_atTop] at htendsto_aux
  obtain ⟨N, hN⟩ := htendsto_aux ε hε
  use ⌈N⌉₊ + 1
  intro n hn
  have hnsucc : n = n - 1 + 1 := by omega
  -- Let us split off the term `k = 0` from the sum
  rw [hnsucc, sum_range_succ']
  push_cast
  rw [mul_zero, zero_add, one_pow, div_one]
  -- Note the following identity for `arctan` which we will use for the `k = 0` term:
  have arctan_2_inv_2 : 2 / π * arctan 2 = 1 -  2 / π * arctan (2⁻¹) := by
    rw [arctan_inv_of_pos (by positivity)]
    field_simp
    ring
  rw [arctan_2_inv_2]
  -- What remains is a telescoping sum -- unfortunately it is a bit cumbersome to convince Lean of this
  have hcast_aux (k : ℕ) : (k : ℝ) + 1 = (((k + 1) : ℕ) : ℝ) := by
    norm_cast
  conv =>
    enter [1, 1, 1]
    conv =>
      enter [2, k]
      rw [hcast_aux, h (by positivity), mul_sub]
      rw [sub_eq_add_neg, ← neg_neg (2 / π * _), add_comm, ← neg_add, ← sub_eq_add_neg]
      conv =>
        enter [1, 1, 2, 1, 2]
        norm_cast
        rw [← mul_one 2, mul_assoc, one_mul, ← mul_add]
    rw [Finset.sum_neg_distrib]
  norm_cast
  let f := fun k : ℕ ↦ 2 / π * arctan (1 / ((2 * (k + 1)) : ℕ))
  rw [sum_range_sub (f := f)]
  simp only [f]
  rw [← hnsucc]
  push_cast
  field_simp
  refine hN n ?_
  calc
    _ ≥ ⌈N⌉₊ + 1 := by assumption
    _ ≥ _ := by linarith only [Nat.le_ceil N]
