import Mathlib

open Polynomial Complex

/- Let $r$, $s$, and $t$ be the three roots of the equation
$$8*x^3 + 1001*x + 2008 = 0.$$

Find $(r+s)^3 + (s+t)^ 3 + (t+r)^3$.
-/
theorem algebra_94009 {r s t : ℂ} {P : Polynomial ℂ} (hP : P = X ^ 3 + C (1001 / 8) * X + C (2008 / 8))
    (hr : P.roots = {r, s, t}) : (r + s) ^ 3 + (s + t) ^ 3 + (t + r) ^ 3 = 753 := by
  -- We first collect elementary facts about our polynomial
  have deg_eq : P.natDegree = 3 := by rw [hP]; compute_degree!
  have posdeg : 0 < P.natDegree := by rw [deg_eq]; norm_num
  have monic : P.Monic := by rw [hP]; monicity!
  have splits := isAlgClosed.splits P
  have nextCoeff_eq : P.nextCoeff = 0 := by rw [nextCoeff_of_natDegree_pos posdeg, deg_eq, hP]; simp
  have coeff_zero_eq : P.coeff 0 = 2008 / 8 := by rw [hP]; simp
  -- By Vieta's formula the sum of the roots of `P` equals 0
  have e1 : r + s + t = 0 := by
    calc
      _ = -(-P.roots.sum) := by simp [hr]; ring
      _ = 0 := by rw [← sum_roots_eq_nextCoeff_of_monic_of_split monic splits, nextCoeff_eq, neg_zero]
  have t_eq : t = -r - s := by
    calc
      _ = (r + s + t) - r - s := by ring
      _ = _ := by rw [e1]; ring
  have neg_t_eq : -t = r + s := by rw [t_eq]; ring
  -- Also by Vieta's formula, the product of the roots of `P` equals `-2008/8`
  have e2 : r * s * t = -2008 / 8 := by
    calc
      _ = - ((-1) ^ P.natDegree * P.roots.prod) := by simp [hr]; rw [deg_eq]; ring
      _ = -2008 / 8 := by rw [← prod_roots_eq_coeff_zero_of_monic_of_splits monic splits, coeff_zero_eq]; ring
  -- Subsituting these into our expression and simplifying gives the answer
  calc
    _ = 3 * r * s * (r + s) := by rw [t_eq]; ring
    _ = 3 * r * s * (-t) := by rw [← neg_t_eq]
    _ = -3 * (r * s * t) := by ring
    _ = 753 := by rw [e2]; norm_num
