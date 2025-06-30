import Mathlib

/-
For positive integers mm and nn such that $m+10 < n+1$, both the mean and the median of the set
$\{m, m + 4, m + 10, n + 1, n + 2, 2 * n\}$ are equal to $n$. What is the value of $m + n$ ?

(A) 20
(B) 21
(C) 22
(D) 23
(E) 24
-/
theorem algebra_98057 {m n : ℕ} (hmean : (m + (m + 4) + (m + 10) + (n + 1) + (n + 2) + (2 * n)) / (6 : ℚ) = n)
    (hmedian : ((m + 10 + (n + 1)) / (2 : ℚ)) = n) : m + n = 21 := by
  -- From the mean equation we get `3 * m + 17 = 2 * n`
  have e₁ : 3 * m + 17 = 2 * n := by
    field_simp at hmean
    norm_cast at hmean
    linarith only [hmean]
  -- From the median equation we get `m + 11 = n`
  have e₂ : m + 11 = n := by
    field_simp at hmedian
    norm_cast at hmedian
    linarith only [hmedian]
  -- Solving this gives `m = 5, n = 16`, so `m + n = 21`
  have m_eq : m = 5 := by linarith only [e₁, e₂]
  have n_eq : n = 16 := by linarith only [e₁, e₂]
  rw [m_eq, n_eq]
