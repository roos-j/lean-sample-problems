import Mathlib

namespace calculus_140111

noncomputable section

open Real intervalIntegral Set

/- Denote the function of interest by `f` -/
def f : ℝ → ℝ := fun x ↦ -x / tan x + log |sin x|

/- A trigonometric lemma missing from Mathlib -/
lemma hasDerivAt_cot {x : ℝ} (hx : sin x ≠ 0) : HasDerivAt cot (-1 / sin x ^ 2) x := by
  rw [show cot = fun x ↦ cos x / sin x by ext; exact cot_eq_cos_div_sin _]
  convert HasDerivAt.div (hasDerivAt_cos _) (hasDerivAt_sin _) hx using 1
  field_simp
  rw [← sin_sq_add_cos_sq]
  ring

/- Compute the derivative of `f` -/
lemma l_hasDerivAt_aux (x : ℝ) (hx : sin x ≠ 0) : HasDerivAt f (x / sin x ^ 2) x := by
  unfold f
  have (x : ℝ) : -x / tan x = -x * cot x := by
    rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin]
    field_simp
  simp_rw [this]
  convert HasDerivAt.add (HasDerivAt.mul (HasDerivAt.neg <| hasDerivAt_id _) (hasDerivAt_cot ?_)) (HasDerivAt.log (hasDerivAt_sin _) ?_) using 1
  · simp
  · field_simp [cot_eq_cos_div_sin]
    ring
  · exact hx
  · exact hx

/-
Calculate the indefinite integral:

$$\int \frac{x}{\sin ^{2} x} d x$$
 -/
theorem calculus_140111 {a : ℝ} : ∃ C, ∀ x, (∀ t ∈ uIcc a x, sin t ≠ 0) → ∫ t in a..x, t / sin t ^ 2 = -x / tan x + log |sin x| + C := by
  -- By the fundamental theorem of calculus it suffices to show that the right hand side is a primitive of the integrand.
  use -(f a)
  intro x hnz
  -- The derivative of `f` is given by `x / sin x ^ 2`
  have haux : EqOn (deriv f) (fun x ↦ x / sin x ^ 2) (uIcc a x) := by
    intro t ht
    rw [HasDerivAt.deriv <| l_hasDerivAt_aux t (hnz t ht)]
  calc
    _ = ∫ t in a..x, deriv f t := by
      apply integral_congr
      intro t ht
      exact (haux ht).symm
    _ = f x - f a := by
      apply integral_deriv_eq_sub
      · intro t ht
        refine (l_hasDerivAt_aux t ?_).differentiableAt
        exact hnz t ht
      · apply ContinuousOn.intervalIntegrable
        refine ContinuousOn.congr ?_ haux
        apply ContinuousOn.div continuousOn_id (ContinuousOn.pow continuousOn_sin 2)
        intro t ht
        have := hnz t ht
        positivity

end

end calculus_140111
