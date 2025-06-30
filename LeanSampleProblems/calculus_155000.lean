import Mathlib

namespace calculus_155000

noncomputable section

open Real intervalIntegral Set

/- Define the functions in question -/
def f : ℝ → ℝ := fun x ↦ -6 / 5 * ((1 + √x) / √x) ^ ((5 : ℝ) / 3)

def f' : ℝ → ℝ := fun x ↦ x ^ ((-11 : ℝ) / 6) * (1 + x ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3)

/- An auxiliary algebraic simplification -/
lemma l_simp_aux {x : ℝ} (hx : 0 < x) : (1 + √x) ^ ((2 : ℝ) / 3) / (x * (x ^ ((5 : ℝ) / 6))) = f' x := by
  field_simp [f', sqrt_eq_rpow]
  conv => enter [2, 2, 1]; rw [← rpow_one x]
  rw [mul_comm, ← mul_assoc, ← rpow_add hx, ← rpow_add hx]
  conv => enter [2, 1, 2]; norm_num
  simp

/- Compute the derivative of the function -/
lemma l_hasDerivAt_aux {x : ℝ} (hx : 0 < x) : HasDerivAt f (f' x) x := by
  convert HasDerivAt.mul (hasDerivAt_const _ _) (.rpow (.div
    (.add (hasDerivAt_const _ 1) (hasDerivAt_sqrt (by positivity)))
      (hasDerivAt_sqrt (by positivity)) (by positivity))
        (hasDerivAt_const _ _) (by positivity)) using 1
  unfold f'
  rw [neg_div, rpow_neg (by positivity)]
  have haux : 2 * x ^ ((1 : ℝ) / 2) * x * 3 * x ^ (((5 : ℝ) - 3) / (2 * 3)) = 6 * x ^ ((11 :  ℝ) / 6) := by
    ring_nf
    conv => enter [1, 1, 1, 2]; rw [← rpow_one x]
    rw [← rpow_add hx, ← rpow_add hx]
    congr
    norm_num
  field_simp [f', sqrt_eq_rpow, ← rpow_mul, ← rpow_natCast, div_rpow, haux]
  ring_nf

/-
Find the indefinite integral:

$$
\int \frac{\sqrt[3]{(1+\sqrt{x})^{2}}}{x \sqrt[6]{x^{5}}} d x
$$
 -/
theorem calculus_155000 {a : ℝ} (ha : 0 < a) : ∃ C, ∀ x > 0,
    ∫ t in a..x, (1 + √t) ^ ((2 : ℝ) / 3) / (t * (t ^ ((5 : ℝ) / 6))) =
    -6 / 5 * ((1 + √x) / √x) ^ ((5 : ℝ) / 3) + C := by
  -- By the fundamental theorem of calculus it suffices to show that the right hand side is a primitive of the integrand.
  use -(f a)
  intro x hx
  -- Auxiliary positivity claim
  have hpos : ∀ t ∈ uIcc a x, 0 < t := by
    intro t ht
    have := ht.1
    calc
      0 < a ⊓ x := by positivity
      _ ≤ t := by assumption
  have hnz : ∀ t ∈ uIcc a x, t ≠ 0 := fun t ht ↦ ne_of_gt <| hpos t ht
  have haux : EqOn (deriv f) f' (uIcc a x) := by
    intro t ht
    rw [HasDerivAt.deriv <| l_hasDerivAt_aux (hpos t ht)]
  calc
    _ = ∫ t in a..x, deriv f t := by
      apply integral_congr
      intro t ht
      simp only [l_simp_aux (hpos t ht)]
      exact (haux ht).symm
     _ = f x - f a := by
      apply integral_deriv_eq_sub
      · intro t ht
        refine (l_hasDerivAt_aux ?_).differentiableAt
        exact hpos t ht
      · apply ContinuousOn.intervalIntegrable
        refine ContinuousOn.congr ?_ haux
        apply ContinuousOn.mul
        · apply ContinuousOn.rpow continuousOn_id continuousOn_const
          exact fun t ht ↦ Or.inl <| hnz t ht
        · apply ContinuousOn.rpow ?_ continuousOn_const
          · exact fun _ _ ↦ Or.inr (by norm_num)
          · apply ContinuousOn.add continuousOn_const
            apply ContinuousOn.rpow continuousOn_id continuousOn_const
            exact fun t ht ↦ Or.inl <| hnz t ht

end

end calculus_155000
