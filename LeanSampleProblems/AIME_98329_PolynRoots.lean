import Mathlib

open Polynomial Complex Finset

/- Consider the polynomials $P(x)=x^6−x^5−x^3−x^2−x$ and $Q(x)=x^4−x^3−x^2−1.$

Given that $z_1,z_2,z_3$ and $z_4$ are the roots of $Q(x)=0$, find
$$P(z_1)+P(z_2)+P(z_3)+P(z_4).$$ -/
theorem algebra_98329 {P Q : Polynomial ℂ} {z : Fin 4 → ℂ}
    (hP : P = X ^ 6 - X ^ 5 - X ^ 3 - X ^ 2 - X)
    (hQ : Q = X ^ 4 - X ^ 3 - X ^ 2 - 1) (hz : Q.roots = {z 0, z 1, z 2, z 3}) :
    P.eval (z 0) + P.eval (z 1) + P.eval (z 2) + P.eval (z 3) = 6 := by
  -- We begin by performing a polynomial division of P by Q to obtain
  have P_eq_mul_Q : P = (X ^ 2 + 1) * Q + X ^ 2 - X + 1 := by rw [hP, hQ]; ring
  have hQz : ∀ i : Fin 4, Q.eval (z i) = 0 := by -- Q is zero at its roots
    intro i
    have : z i ∈ Q.roots := by rw [hz]; fin_cases i <;> simp
    exact (mem_roots'.mp this).2
  -- Plugging in the roots of `Q` we can write the expression in question as follows
  have res_eq : P.eval (z 0) + P.eval (z 1) + P.eval (z 2) + P.eval (z 3) = (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2)
    - (z 0 + z 1 + z 2 + z 3) + 4 := by
    rw [P_eq_mul_Q]
    simp [hz, hQz]
    ring
  -- We have Newton's identity:
  have sum_sq_eq : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 = (z 0 + z 1 + z 2 + z 3) ^ 2
    - 2 * (z 0 * z 1 + z 0 * z 2 + z 0 * z 3 + z 1 * z 2 + z 1 * z 3 + z 2 * z 3) := by ring
  have deg_Q : Q.natDegree = 4 := by rw [hQ]; compute_degree!
  have leadCoeff : Q.leadingCoeff = 1 := by rw [leadingCoeff, deg_Q, hQ]; compute_degree!
  have roots_card : Q.roots.card = Q.natDegree := by rw [hz, deg_Q]; simp
  -- Applying Vieta's formula for the 2nd coefficient of Q:
  have e2 : z 0 * z 1 + z 0 * z 2 + z 0 * z 3 + z 1 * z 2 + z 1 * z 3 + z 2 * z 3 = -1 := by
    have coeff_two : Q.coeff 2 = -1 := by rw [hQ]; simp; compute_degree
    have ev := coeff_eq_esymm_roots_of_card (k := 2) roots_card (by rw [deg_Q]; norm_num)
    rw [deg_Q, leadCoeff, hz, coeff_two] at ev
    rw [ev]
    simp [Multiset.esymm, Multiset.powersetCard_one]
    ring
  -- Applying Vieta's formula for the 3rd coefficient of Q:
  have e1 : z 0 + z 1 + z 2 + z 3 = 1 := by
    have deg_pos : 0 < Q.natDegree := by rw [deg_Q]; positivity
    have monic : Q.Monic := by rw [hQ]; monicity!
    have splits := isAlgClosed.splits Q
    have nextCoeff_eq : Q.nextCoeff = -1 := by rw [nextCoeff_of_natDegree_pos deg_pos, deg_Q, hQ]; simp [coeff_one]
    calc
      _ = -(-Q.roots.sum) := by rw [hz]; simp; ring
      _ = _ := by rw [← sum_roots_eq_nextCoeff_of_monic_of_split monic splits, nextCoeff_eq]; norm_num
  -- Putting everything together we obtain the claim
  rw [res_eq, sum_sq_eq, e2, e1]; norm_num
