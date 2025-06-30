import Mathlib

/- Prove that any integer can be expressed as the sum of five cubes of integers.
(Former Soviet Union University Mathematics Competition, 1977) -/
theorem number_theory_140248 (n : ℤ) :
    ∃ x y z w v : ℤ, n = x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3 + v ^ 3 := by
  -- Observe that every multiple of `6` can be written as a sum of `4` cubes because
  -- 6 * m = (m + 1) ^ 3 + (-m) ^ 3 + (-m) ^ 3 + (m - 1) ^ 3
  -- Then we consider each possible remainder modulo `6` separately
  let m := n / 6
  have n_eq : n = 6 * m + n % 6 := Eq.symm (Int.ediv_add_emod n 6)
  obtain h|h|h|h|h|h := show n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 by omega
  · use m + 1, -m, -m, m - 1, 0
    rw [n_eq, h]
    ring
  · use m + 1, -m, -m, m - 1, 1
    rw [n_eq, h]
    ring
  · use m, -m + 1, -m + 1, m - 2, 2
    rw [n_eq, h]
    ring
  · use m - 3, -m + 4, -m + 4, m - 5, 3
    rw [n_eq, h]
    ring
  · use m + 3, -m - 2, -m - 2, m + 1, -2
    rw [n_eq, h]
    ring
  · use m + 2, -m - 1, -m - 1, m, -1
    rw [n_eq, h]
    ring
