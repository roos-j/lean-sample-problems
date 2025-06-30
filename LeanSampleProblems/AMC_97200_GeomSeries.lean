import Mathlib

open Real

/- For some positive integer $k$, the repeating base-$k$ representation of the (base-ten) fraction $\frac{7}{51}$​
is $0.\overline{23}_k$. What is $k$ ?

(A) 13
(B) 14
(C) 15
(D) 16
(E) 17 -/
theorem number_theory_97200 (k : ℕ) (hk : k = 16) :
    (7 / 51 : ℝ) = 2 * ∑' n : ℕ, (1 : ℝ) / k ^ (2 * n + 1) + 3 * ∑' n : ℕ, (1 : ℝ) / k ^ (2 * n + 2) := by
  -- We use the geometric series formula on both sums and check that the equation holds for `k = 16`
  -- This is a reasonable encoding of the posed problem since we may assume by design that only one of the answers is correct.
  have aux1 (n : ℕ): (1 : ℝ) / k ^ (2 * n + 1) = ((1 : ℝ) / k) • (1 / k ^ 2) ^ n := by field_simp; ring
  have aux2 (n : ℕ): (1 : ℝ) / k ^ (2 * n + 2) = ((1: ℝ) / k) ^ 2 • (1 / k ^ 2) ^ n := by field_simp; ring
  simp_rw [aux1, aux2]
  rw [tsum_const_smul _ <| summable_geometric_of_norm_lt_one (by rw [hk]; norm_num)]
  rw [tsum_const_smul _ <| summable_geometric_of_norm_lt_one (by rw [hk]; norm_num)]
  rw [tsum_geometric_of_lt_one (by positivity) (by rw [hk]; norm_num)]
  rw [hk]
  norm_num
