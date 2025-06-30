import Mathlib

open Topology Filter Real Finset Classical

noncomputable section

/- For convenience define shortcuts for the maximum norm of a finite sequence (will only be used for nonnegative seq) -/
def maxNorm {k : ℕ} (x : Fin (k + 1) → ℝ) : ℝ := x <| choose <| exists_max_image univ x univ_nonempty

lemma le_maxNorm {k : ℕ} (x : Fin (k + 1) → ℝ) : ∀ i, x i ≤ maxNorm x := fun i ↦ (choose_spec <| exists_max_image univ x univ_nonempty).2 i <| mem_univ _

/- ℓᴾ norm of `x` is bounded by a constant times the maximum norm. -/
lemma lp_norm_lesssim_maxNorm {k : ℕ} {p : ℝ} (hp : 0 < p) (x : Fin (k + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) : (∑ i, x i ^ p) ^ (1 / p) ≤ (k + 1) ^ (1 / p) * maxNorm x := by
  have : 0 ≤ ∑ i, x i ^ p := by
    apply sum_nonneg
    intro i _
    have := hx i
    positivity
  have : 0 ≤ maxNorm x := hx _
  calc
    _ ≤ ((k + 1) * maxNorm x ^ p) ^ (1 / p) := by
      gcongr
      convert sum_le_card_nsmul univ (fun i ↦ x i ^ p) (maxNorm x ^ p) ?_ using 1
      · simp
      · intro i _
        exact rpow_le_rpow (hx i) (le_maxNorm _ _) (by positivity)
    _ = _ := by
      rw [mul_rpow (by positivity) (by positivity)]
      rw [← rpow_mul (by positivity), one_div, mul_inv_cancel₀ (by positivity), rpow_one]

/- Maximum norm is bounded by the ℓⁿ norm -/
lemma maxNorm_le_lp_norm {k : ℕ} {p : ℝ} (hp : 0 < p) (x : Fin (k + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) : maxNorm x ≤ (∑ i, x i ^ p) ^ (1 / p) := by
  have : 0 ≤ maxNorm x := hx _
  calc
    _ = (maxNorm x ^ p) ^ (1 / p) := by
      rw [← rpow_mul (by positivity), one_div, mul_inv_cancel₀ (by positivity), rpow_one]
    _ ≤ _ := by
      gcongr
      have : ∀ i ∈ univ, 0 ≤ x i ^ p := fun i _ ↦ by have := hx i; positivity
      exact single_le_sum this (mem_univ _)

/- Auxiliary limit -/
lemma l_tendsto_aux (k : ℕ) : Tendsto (fun n ↦ ((k + 1) : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 1) := by
  convert Tendsto.comp (continuousAt_const_rpow (a := k + 1) (b := 0) (by positivity)) tendsto_inv_atTop_zero using 1
  · ext; simp
  · simp

/- Let the random variable $\xi$ take a finite number of values $x_{1}, \ldots, x_{k} \geqslant 0$. Show that

$$
\lim _{n \rightarrow \infty}\left(E \xi^{n}\right)^{1 / n}=\max \left\{x_{1}, \ldots, x_{k}\right\}
$$
 -/
theorem algebra_183002 {k : ℕ} {x : Fin (k + 1) → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    Tendsto (fun n ↦ (∑ i, x i ^ n) ^ ((1 : ℝ) / n)) atTop (𝓝 (maxNorm x)) := by
  -- By `lp_norm_lesssim_maxNorm`, `maxNorm_le_lp_norm` and the limit `l_tendsto_aux`,
  -- the claim follows by the "squeeze theorem".
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have maxNorm_nonneg : 0 ≤ maxNorm x := hx _
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (l_tendsto_aux k)) (ε / (1 + maxNorm x)) (by positivity)
  use N ⊔ 1
  intro n hn
  simp only [ge_iff_le, sup_le_iff] at hn
  specialize hN n hn.1
  have n_pos : 0 < n := by have := hn.2; positivity
  apply abs_lt.mpr
  constructor
  · calc
      _ < (0 : ℝ) := by simp only [Left.neg_neg_iff, hε]
      _ ≤ _ := by linarith only [maxNorm_le_lp_norm n_pos x hx]
  · calc
      _ ≤ (k + 1) ^ ((1 : ℝ) / n) * maxNorm x - maxNorm x := by
        gcongr
        exact lp_norm_lesssim_maxNorm n_pos x hx
      _ = maxNorm x * ((k + 1) ^ ((1 : ℝ) / n) - 1) := by ring
      _ ≤ maxNorm x * (ε / (1 + maxNorm x)) := by
        gcongr (maxNorm x) * ?_
        exact le_of_lt (abs_lt.mp hN).2
      _ < (1 + maxNorm x) * (ε / (1 + maxNorm x)) := by gcongr; linarith only
      _ = _ := by field_simp

end
