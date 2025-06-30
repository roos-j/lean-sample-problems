import Mathlib

open Polynomial

/- $X$ and $Y$ are the roots of the equation $t^{2}-c t-c=0$. Prove that the inequality $X^{3}+Y^{3}+(X Y)^{3} \geqslant 0$ holds. -/
theorem inequalities_205736 {c x y: ℝ}
    (h : (X ^ 2 + (C (-c)) * X + C (- c)).roots = {x, y}) :
    x ^ 3 + y ^ 3 + (x * y) ^ 3 ≥ 0 := by
  -- We begin by collecting elementary facts about our quadratic polynomial
  let P := X ^ 2 + (C (-c)) * X + C (- c)
  have P_roots : P.roots = {x, y} := by simp only [P]; rw [h]
  have P_deg : P.natDegree = 2 := by simp only [P]; compute_degree!
  have P_coeff_zero : P.coeff 0 = -c := by simp [P]
  have P_nextCoeff : P.nextCoeff = -c := by rw [nextCoeff_of_natDegree_pos (by positivity)]; rw [P_deg]; simp [P]
  have monic : P.Monic := by simp [P]; monicity!
  have splits := splits_iff_card_roots.mpr (show P.roots.card = P.natDegree by simp only [P]; rw [P_deg, h]; simp)
  -- By assumption we have `x + y = c`
  have e1 : x + y = c := by
    have := sum_roots_eq_nextCoeff_of_monic_of_split monic splits
    rw [P_nextCoeff, P_roots] at this
    simp at this
    linarith only [this]
  -- And also `x * y = -c`
  have e2 : x * y = -c := by
    have := prod_roots_eq_coeff_zero_of_monic_of_splits monic splits
    rw [P_coeff_zero, P_roots, P_deg] at this
    simp at this
    linarith only [this]
  -- Then we can calculate that the expression in question equals `3 c ^ 2 ≥ 0`
  calc
    _ = (x + y) ^ 3 - 3 * x ^ 2 * y - 3 * x * y ^ 2 + (x * y) ^ 3 := by ring
    _ = c ^ 3 - 3 * x * (-c) - 3 * y * (-c) + (-c) ^ 3 := by
      congr! 1; swap; rw [← e2]
      congr! 1; swap; rw [← e2]; ring
      congr! 1; rw [e1]; rw [← e2]; ring
    _ = 3 * c * (x + y) := by ring
    _ = 3 * c ^ 2 := by rw [e1]; ring
    _ ≥ 0 := by simp [sq_nonneg]
