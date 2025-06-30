import Mathlib

/- What is the relationship between the sets $M=\{u \mid u=12 m+8 n+4 l, m, n, l \in \mathbf{Z}\}$, $N=\{u \mid u=20 p+16 q+12 r, p$, $q, r \in Z\}$ ? -/
theorem number_theory_261447 {M N : Set ℤ} (hM : M = {u : ℤ | ∃ m n l, u = 12 * m + 8 * n + 4 * l})
  (hN : N = {u : ℤ | ∃ p q r, u = 20 * p + 16 * q + 12 * r}) : M = N := by
  -- We prove that `M ⊆ N` and vice versa by setting appropriate multiples of the variables
  apply le_antisymm
  · -- If `u ∈ M` we set `p = l + n, q = -l, r = m - n` to show `u ∈ N`
    rintro u hu
    rw [hM] at hu
    obtain ⟨m, n, l, h⟩ := hu
    rw [hN]
    use l + n, -l, m - n
    rw [h]
    ring
  · -- If `u ∈ N` we set `m = r, n = 2 * q, l = 5 * p`
    rintro u hu
    rw [hN] at hu
    obtain ⟨p, q, r, h⟩ := hu
    rw [hM]
    use r, 2 * q, 5 * p
    rw [h]
    ring
