import Mathlib

namespace inequalities_24812

noncomputable section

open Real Set Finset

/- We define an auxiliary function -/
def f : ℝ → ℝ := fun x ↦ 1 / (1 + exp x)

/- First derivative of the function -/
def f' : ℝ → ℝ := fun x ↦ -exp x / (1 + exp x) ^ 2

/- We prove that `f` is differentiable with the claimed derivative -/
lemma l_hasDerivAt_aux {x : ℝ} : HasDerivAt f (f' x) x := by
  convert HasDerivAt.div (hasDerivAt_const _ _)
    (HasDerivAt.add (hasDerivAt_const _ _) (hasDerivAt_exp _)) ?_ using 1
  · simp; rfl
  · positivity

/- Second derivative of the function -/
def f'' : ℝ → ℝ := fun x ↦ exp x * (exp x - 1) / (1 + exp x) ^ 3

/- We prove that the derivative of `f` is differentiable with the claimed derivative -/
lemma l_hasDerivAt_deriv_aux {x : ℝ} : HasDerivAt (deriv f) (f'' x) x := by
  have hf' : deriv f = f' := by
    ext; exact l_hasDerivAt_aux.deriv
  rw [hf']
  convert HasDerivAt.div (HasDerivAt.neg <| hasDerivAt_exp _)
    (HasDerivAt.pow _ (HasDerivAt.add (hasDerivAt_const _ _) (hasDerivAt_exp _))) ?_ using 1
  · field_simp [f'']
    ring
  · positivity

/- We prove that `f` is convex on `[0, ∞)` by the second derivative test -/
lemma l_convex_aux : ConvexOn ℝ (Ici 0) (fun x ↦ 1 / (1 + exp x)) := by
  apply convexOn_of_deriv2_nonneg'
  · exact convex_Ici _
  · apply Differentiable.differentiableOn
    exact fun _ ↦ l_hasDerivAt_aux.differentiableAt
  · apply Differentiable.differentiableOn
    exact fun _ ↦ l_hasDerivAt_deriv_aux.differentiableAt
  · intro x hx
    have h : 0 ≤ f'' x := by
      simp only [f'']
      apply div_nonneg
      · apply mul_nonneg
        · exact exp_nonneg _
        · linarith only [one_le_exp hx]
      · positivity
    convert h
    ext x
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
    exact HasDerivAt.deriv l_hasDerivAt_deriv_aux

/- Let $r_{1}, r_{2}, \ldots, r_{n}$ be real numbers greater than or equal to 1 . Prove that
$$
 \frac{1}{r_{1}+1}+\frac{1}{r_{2}+1}+\cdots+\frac{1}{r_{n}+1} \geq \frac{n}{\sqrt[n]{r_{1} r_{2} \cdots r_{n}}+1}
$$
 -/
theorem inequalities_24812
    {n : ℕ}
    {r : Fin n → ℝ}
    (hn : 0 < n)
    (hr : ∀ i, 1 ≤ r i) :
    ∑ i, (1 / (r i + 1)) ≥ (n / ( (∏ i, r i) ^ ((1 : ℝ) / n) + 1)) := by
  -- Let us substitute `r i = exp (x i)`
  let x : Fin n → ℝ := fun i ↦ log (r i)
  have x_nonneg {i : Fin n} := log_nonneg <| hr i
  have r_eq {i : Fin n} : r i = exp (x i) := by simp [x, exp_log (show 0 < r i by linarith only [hr i])]
  -- Then the claim follows from Jensen's inequality and convexity of `f`
  have h := l_convex_aux.map_sum_le (p := x) (w := fun _ ↦ (1 : ℝ) / n) (t := univ) ?_ ?_ ?_
  · simp_rw [r_eq]
    rw [← exp_sum, ← exp_mul, mul_comm, add_comm _ 1]
    conv => enter [1, 2, i]; rw [add_comm]
    simp_rw [smul_eq_mul] at h
    rw [← mul_sum, ← mul_sum] at h
    apply le_of_mul_le_mul_left (a0 := show 0 < (1 : ℝ) / n by positivity)
    field_simp
    field_simp at h
    exact h
  · exact fun _ _ ↦ by positivity
  · field_simp
  · exact fun _ _ ↦ x_nonneg

end

end inequalities_24812
