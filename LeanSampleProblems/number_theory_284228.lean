import Mathlib

/- Let $M=\{u \mid u=12 m+8 n+4 l, m, n, l \in \mathbf{Z}\}, N=\{u \mid u=20 p+16 q+12 r, p$, $q, r \in \mathbf{Z}\}$.
Then $M=N$. -/
theorem number_theory_284228 :
    {u : ℤ | ∃ m n l : ℤ, u = 12 * m + 8 * n + 4 * l} =
      {u : ℤ | ∃ p q r : ℤ, u = 20 * p + 16 * q + 12 * r} := by
  -- We show that the two sets are equal by showing both inclusions
  ext u
  constructor
  · -- We first show `⊆` by setting `p = l + n, q = -l, r = m - n`
    rintro ⟨m, n, l, h⟩
    use l + n, -l, m - n
    rw [h]
    ring
  · -- Then we show `⊇` by setting `m = r, n = 2 * q, l = 5 * p`
    rintro ⟨p, q, r, h⟩
    use r, 2 * q, 5 * p
    rw [h]
    ring
