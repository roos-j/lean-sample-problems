import Mathlib


open Finset


/- Given the sequence $\left\{a_{n}\right\}$ with the first term being 2, and satisfying

$$6 S_{n}=3 a_{n+1}+4^{n}-1,$$

where $S_n = \sum_{i=1}^n a_i$.

Then the maximum value of $S_{n}$ is $35$. -/

theorem algebra_281101 {a : ℕ → ℝ} (ha : a 1 = 2)
    (h : ∀ n, 6 * ∑ i in range n, a (i + 1) = 3 * a (n + 1) + 4 ^ n - 1) :
    IsGreatest {∑ i in range n, a (i + 1) | n} 35 := by
  -- We first determine the sequence `a`:
  have a_eq (n : ℕ) : a (n + 1) = 3 ^ (n + 1) - 4 ^ n := by
    -- Substracting `h n` and `h (n + 1)` we get the following recursion
    have ha_rec (n : ℕ) : a (n + 2) = 3 * a (n + 1) - 4 ^ n := by
      suffices h : 6 * a (n + 1) = 3 * a (n + 2) - 3 * a (n + 1) + 3 * 4 ^ n by
        linarith only [h]
      calc
        _ = 6 * ∑ i in range (n + 1), a (i + 1) - 6 * ∑ i in range n, a (i + 1) := by
          rw [sum_range_succ]
          ring
        _ = _ := by
          rw [h n, h (n + 1)]
          ring

    -- Then the formula for `a` follows by induction
    induction' n with n ih
    · norm_num; exact ha
    · rw [add_assoc, ha_rec n, ih]
      ring

  -- Then we see that `a n` is eventually negative, leaving only finitely many values to check
  have a_neg (n : ℕ) (hn : 4 ≤ n) : a (n + 1) < 0 := by
    rw [a_eq]
    induction' n, hn using Nat.le_induction with n hn ih
    · norm_num
    · rw [pow_add, pow_one, pow_add 4, pow_one]
      calc
        _ < (4 : ℝ) ^ n * 3 - 4 ^ n * 4 := by
          gcongr
          linarith only [ih]
        _ = - (4 : ℝ) ^ n := by ring
        _ < 0 := by
          linarith only [pow_pos (show 0 < (4 : ℝ) by norm_num) n]

  constructor
  · -- First, `35 = S 4`
    use 4
    simp [sum_range_succ, a_eq]
    norm_num
  · -- Next, the sum is always `≤ 35`
    rintro S ⟨n, hn⟩
    rw [← hn]
    by_cases hn' : n < 5
    · interval_cases n
        <;> {
          simp [sum_range_succ, a_eq]
          try norm_num
        }
    · push_neg at hn'
      calc
        _ = ∑ i ∈ range 4, a (i + 1) + ∑ i ∈ Ico 4 n, a (i + 1) := by
          rw [← sum_range_add_sum_Ico]
          clear * - hn'; omega
        _ ≤ ∑ i ∈ range 4, a (i + 1) + 0 := by
          gcongr
          apply sum_nonpos
          intro i hi
          apply le_of_lt
          refine a_neg _ ?_
          simp only [mem_Ico] at hi
          omega
        _ = _ := by
          simp [sum_range_succ, a_eq]
          norm_num
