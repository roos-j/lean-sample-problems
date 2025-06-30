import Mathlib

namespace calculus_139988

open Real intervalIntegral Set

/- Two auxiliary facts -/
lemma l_aux_ne_zero {x : ℝ} (hx : 1 / 3 < x) : 2 * √(3 * x - 1) ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  apply (sqrt_ne_zero ?_).mpr
    <;> linarith only [hx]

lemma l_aux_ne_zero2 {x : ℝ} (hx : 1 / 3 < x) : 2 * x * √(3 * x - 1) ≠ 0 := by
  rw [mul_comm 2, mul_assoc]
  exact mul_ne_zero (by linarith only [hx]) (l_aux_ne_zero hx)

/- Calculate the derivative of a function involving arctan and square root -/
lemma l_hasDerivAt_arctan_sqrt {x : ℝ} (hx : 1 / 3 < x) : HasDerivAt (fun x ↦ arctan (√(3 * x - 1))) (1 / (2 * x * √(3 * x - 1))) x := by
  convert HasDerivAt.arctan (.sqrt (.sub (.const_mul 3 (hasDerivAt_id _)) (hasDerivAt_const _ _)) ?_) using 1
  · have := l_aux_ne_zero hx
    have := l_aux_ne_zero2 hx
    have : (1 + √(3 * x - 1) ^ 2) * (2 * √(3 * x - 1)) ≠ 0 := by positivity
    have : 0 < 3 * x - 1 := by linarith only [hx]
    field_simp [sq_sqrt (by positivity)]
    ring
  · rw [id]
    linarith only [hx]

/- Calculate the derivative of a function involving square root -/
lemma l_hasDerivAt_sqrt {x : ℝ} (hx : 1 / 3 < x) : HasDerivAt (fun x ↦ 1 / 3 * √(3 * x - 1)) (1 / (2 * √(3 * x - 1))) x := by
  convert HasDerivAt.const_mul (1 / 3) (.sqrt (.sub (.const_mul 3 (hasDerivAt_id _)) (hasDerivAt_const _ _)) ?_) using 1
  · have := l_aux_ne_zero hx
    field_simp
  · rw [id]
    linarith only [hx]

/- Calculate the derivative of the function in question -/
lemma l_hasDerivAt_f {x : ℝ} (hx : 1 / 3 < x) : HasDerivAt (fun x ↦ x * arctan (√(3 * x - 1)) - √(3 * x - 1) / 3) (arctan (√(3 * x - 1))) x := by
  convert HasDerivAt.sub (.mul (hasDerivAt_id _) (l_hasDerivAt_arctan_sqrt hx)) (l_hasDerivAt_sqrt hx) using 1
  · ext
    field_simp
  · have := l_aux_ne_zero hx
    have := l_aux_ne_zero2 hx
    field_simp
    ring

/- Show continuity of the following function -/
lemma l_aux_continuousOn : Continuous (fun x => arctan √(3 * x - 1)) := by -- `fun_prop` should be able to do this, but it can't
  apply Continuous.comp (g := arctan)
  · exact continuous_arctan
  · fun_prop

lemma l_aux_of_mem_uIcc {a x t : ℝ} (ha : 1 / 3 < a) (hx : 1 / 3 < x) (ht : t ∈ uIcc a x) : 1 / 3 < t := by
  rw [mem_uIcc] at ht
  obtain ⟨_, _⟩ | ⟨_, _⟩ := ht
    <;> linarith

/-
Calculate the indefinite integral:

$$\int \operatorname{arctg} \sqrt{3 x-1} \, d x$$
 -/
theorem calculus_139988 (a : ℝ) (ha : 1 / 3 < a) : ∃ C : ℝ, ∀ x > 1 / 3, ∫ t in a..x, arctan (√(3 * t - 1)) = x * arctan (√(3 * x - 1)) - √(3 * x - 1) / 3 + C := by
  -- To avoid technicalities not in the spirit of the problem we assume `1 / 3 < a` to avoid the singularity at `x = 1 / 3`
  -- We will use the fundamental theorem of calculus
  let f : ℝ → ℝ := fun x ↦ x * arctan (√(3 * x - 1)) - √(3 * x - 1) / 3
  let f' : ℝ → ℝ := fun x ↦ arctan (√(3 * x - 1))
  -- We have proved above that `f'` is indeed the derivative of `f`
  have hf (x : ℝ) (hx : 1 / 3 < x) : HasDerivAt f (f' x) x := l_hasDerivAt_f hx
  use -f a
  intro x hx
  calc
    _ = ∫ t in a..x, deriv f t := by
      apply integral_congr
      intro t ht
      rw [HasDerivAt.deriv <| hf t _]
      exact l_aux_of_mem_uIcc ha hx ht
    _ = f x - f a := by
      apply integral_deriv_eq_sub
      · intro t ht
        refine (hf t ?_).differentiableAt
        exact l_aux_of_mem_uIcc ha hx ht
      · apply ContinuousOn.intervalIntegrable
        have haux : EqOn (deriv f) f' (uIcc a x) := by
          intro t ht
          rw [HasDerivAt.deriv <| hf t _]
          exact l_aux_of_mem_uIcc ha hx ht
        refine ContinuousOn.congr ?_ haux
        exact Continuous.continuousOn l_aux_continuousOn

end calculus_139988
