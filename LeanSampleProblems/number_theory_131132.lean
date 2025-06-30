import Mathlib

open Int Finset

/- Prove: If integers $a_{k}(k=1,2,3,4,5)$ satisfy $9 \mid a_{1}^{3}+a_{2}^{3}+a_{3}^{3}+a_{4}^{3}+$. $a_{5}^{3}$, then $3 \mid a_{1} a_{2} a_{3} a_{4} a_{5}$. -/
theorem number_theory_131132 (a : Fin 5 → ℤ) (h : 9 ∣ ∑ k : Fin 5, (a k)^3) :
    3 ∣ ∏ k : Fin 5, a k := by
  -- First prove an auxiliary statement that seems to be missing from Mathlib
  have pow_emod (a: ℤ) (b : ℕ) (n : ℤ) : a ^ b % n = (a % n) ^ b % n := by
    induction b with
    | zero => rfl
    | succ b ih => simp [Int.pow_succ, Int.mul_emod, ih]
  -- An integer that is not divisible by 3, when cubed and divided by 9, leaves a remainder of 1 or -1.
  have cubemod9 {n : ℤ} (h : n % 3 ≠ 0) : (n ^ 3) % 9 = 1 ∨ (n ^ 3) % 9 = -1 % 9 := by
    rw [show n % 3 = (n % 9) % 3 by omega] at h
    have : n % 9 < 9 := Int.emod_lt_of_pos _ (by norm_num)
    have : 0 ≤ n % 9 := Int.emod_nonneg _ (by norm_num)
    rw [pow_emod]
    interval_cases n % 9 <;> {
      simp at h
      try norm_num
    }
  apply dvd_of_emod_eq_zero
  -- Consider two cases:
  by_cases h' : ∃ k, a k % 3 = 0
  · -- If one of the numbers is divisible by three we are done:
    obtain ⟨k, hk⟩ := h'
    rw [prod_int_mod, ← Finset.prod_erase_mul (h := mem_univ k), hk]
    simp
  · -- Now assume that none of the numbers is divisible by three
    push_neg at h'
    have := emod_eq_zero_of_dvd h
    rw [sum_int_mod] at this
    rw [Fin.sum_univ_five] at this
    -- Then the sum of cubes modulo `9` is a sum of five `±1`s. This can't be equal to zero, contradiction!
    obtain ⟨h0|h0, h1|h1, h2|h2, h3|h3, h4|h4⟩ := And.intro (cubemod9 (h' 0)) <|
      And.intro (cubemod9 (h' 1)) <|
      And.intro (cubemod9 (h' 2)) <|
      And.intro (cubemod9 (h' 3)) (cubemod9 (h' 4))
      <;> {
        rw [h0, h1, h2, h3, h4] at this
        contradiction
      }
