import Mathlib

/- Determine all prime numbers $p$ for which the number $2 p^{4}-p^{2}+16$ is a perfect square. -/
theorem number_theory_103808 (p : ℕ) (hp : p.Prime) :
    IsSquare ((2 : ℤ) * p ^ 4 - p ^ 2 + 16) ↔ p = 3 := by
  -- First prove a missing Mathlib lemma:
  have Int.pow_emod (a: ℤ) (b : ℕ) (n : ℤ) : a ^ b % n = (a % n) ^ b % n := by
    induction b with
    | zero => rfl
    | succ b ih => simp [Int.pow_succ, Int.mul_emod, ih]
  -- It is clear that `p = 3` is a solution.
  constructor; swap; focus { intro hp; rw [hp]; use 13; norm_num }
  -- It remains to show that `p = 3` is the only solution
  intro h
  obtain ⟨k, hk⟩ := h
  by_cases h3 : p = 3; assumption
  -- This follows by observing that the left hand side has remainder 2 modulo 3
  have e : (2 * p ^ 4 - p ^ 2 + 16) % 3 = (2 : ℤ) := by
    rw [Int.add_emod, Int.sub_emod, Int.mul_emod, Int.pow_emod _ 4, Int.pow_emod _ 2]
    have : (p : ℤ) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have : 1 ≤ (p : ℤ) % 3 := by -- Since `p` is prime and not `3` the remainder can't be `0`
      by_contra h
      have : (p : ℤ) % 3 = 0 := by omega
      simp at this
      norm_cast at this
      exact h3 (Nat.dvd_prime_two_le hp (by norm_num) |>.mp this).symm
    interval_cases (p : ℤ) % 3 <;> norm_num
  -- Thus it cannot be equal to a square
  have hk3 : 2 = k ^ 2 % 3 := by rw [← e, hk, pow_two]
  have : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  rw [Int.pow_emod] at hk3
  interval_cases (k : ℤ) % 3 <;> norm_num at hk3
