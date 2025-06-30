import Mathlib

open Polynomial Complex

/- The numbers $u, v, w$ are roots of the equation $x^{3}-3 x-1=0$. Find $u^{9}+v^{9}+w^{9}$.  -/
theorem algebra_257461 {u v w : ℂ} {P : ℂ[X]} (hP : P = X ^ 3 - 3 * X - 1)
    (hPr : P.roots = {u, v, w}) : u ^ 9 + v ^ 9 + w ^ 9 = 246 := by
  -- First collect some basic facts about our polynomial
  have monic : P.Monic := by rw [hP]; monicity!
  have deg : P.natDegree = 3 := by rw [hP]; compute_degree!
  have coeff_one : P.coeff 1 = -3 := by simp [hP]; compute_degree
  have nextCoeff : P.nextCoeff = 0 := by rw [nextCoeff_of_natDegree_pos (by positivity), deg, hP]; simp [coeff_X]; compute_degree
  have splits := isAlgClosed.splits P
  have ne_zero : P ≠ 0 := Monic.ne_zero_of_ne (by norm_num) monic
  -- By Vieta's formulas we have:
  have v1 : u + v + w = 0 := by
    have := sum_roots_eq_nextCoeff_of_monic_of_split monic splits
    rw [nextCoeff, hPr] at this
    simp at this
    linear_combination this
  have v2 : u * v + v * w + u * w = - 3 := by
    have := coeff_eq_esymm_roots_of_splits splits (show 1 ≤ P.natDegree by rw [deg]; norm_num)
    rw [coeff_one, deg, show P.leadingCoeff = 1 by assumption, hPr] at this
    simp [Multiset.esymm, Multiset.powersetCard_one] at this
    rw [this]
    ring
  -- Now define the sequence of power sums
  let S (n : ℕ) := u ^ n + v ^ n + w ^ n
  -- Let us record the values for `n = 0, 1, 2`
  have S_zero : S 0 = 3 := by simp only [S]; norm_num
  have S_one : S 1 = 0 := by simp [S, v1]
  have S2 : S 2 = 6 := by calc
    _ = (u + v + w) ^ 2 - 2 * (u * v + v * w + u * w) := by ring
    _ = _ := by rw [v1, v2]; norm_num

  -- `u, v, w` are roots by assumption
  have hu : u ^ 3 - 3 * u - 1 = 0 := by calc
      _ = P.eval u := by rw [hP]; simp
      _ = 0 := by refine IsRoot.eq_zero ?_; apply (mem_roots ne_zero).mp; rw [hPr]; simp
  have hv : v ^ 3 - 3 * v - 1 = 0 := by calc
      _ = P.eval v := by rw [hP]; simp
      _ = 0 := by refine IsRoot.eq_zero ?_; apply (mem_roots ne_zero).mp; rw [hPr]; simp
  have hw : w ^ 3 - 3 * w - 1 = 0 := by calc
      _ = P.eval w := by rw [hP]; simp
      _ = 0 := by refine IsRoot.eq_zero ?_; apply (mem_roots ne_zero).mp; rw [hPr]; simp

  -- We can compute all the `S n` recursively as follows:
  have S_eq (n : ℕ) : S (n + 3) = 3 * S (n + 1) + S n := by
    simp only [S]
    have eu : u ^ (n + 3) = 3 * u ^ (n + 1) + u ^ n := by
      calc
        _ = (u ^ 3 - 3 * u - 1) * u ^ n + 3 * u ^ (n + 1) + u ^ n := by ring
        _ = 3 * u ^ (n + 1) + u ^ n := by rw [hu]; simp
    have ev : v ^ (n + 3) = 3 * v ^ (n + 1) + v ^ n := by
      calc
        _ = (v ^ 3 - 3 * v - 1) * v ^ n + 3 * v ^ (n + 1) + v ^ n := by ring
        _ = 3 * v ^ (n + 1) + v ^ n := by rw [hv]; simp
    have ew : w ^ (n + 3) = 3 * w ^ (n + 1) + w ^ n := by
      calc
        _ = (w ^ 3 - 3 * w - 1) * w ^ n + 3 * w ^ (n + 1) + w ^ n := by ring
        _ = 3 * w ^ (n + 1) + w ^ n := by rw [hw]; simp
    rw [eu, ev, ew]; ring

  -- From this we can compute `S 3` through `S 7`
  have S3 : S 3 = 3 := by rw [S_eq, S_one, S_zero]; norm_num
  have S4 : S 4 = 18 := by rw [S_eq, S2, S_one]; norm_num
  have S5 : S 5 = 15 := by rw [S_eq, S3, S2]; norm_num
  have S6 : S 6 = 57 := by rw [S_eq, S4, S3]; norm_num
  have S7 : S 7 = 63 := by rw [S_eq, S5, S4]; norm_num

  -- This allows us to compute `S 9` as desired
  change S 9 = 246
  rw [S_eq, S7, S6]; norm_num
