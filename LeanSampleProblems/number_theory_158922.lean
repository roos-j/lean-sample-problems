import Mathlib

open Nat Finset

/- Determine all pairs $(n, m)$ of non-negative integers such that

$$\sum_{i=1}^{n} i=25^{m}+2.$$
 -/
theorem number_theory_158922 (n m : ℕ) :
    ∑ i ∈ range (n + 1), i = 25 ^ m + 2 ↔ (n, m) = (2, 0) := by
  constructor
  · intro h
    -- Let us first use Gauss' identity to simplify the expression
    rw [sum_range_id] at h
    simp
    match m with
    | 0 => -- Suppose that `m = 0`
      refine ⟨?_, rfl⟩
      simp at h
      -- Then we have `n = 2`.
      obtain hn|hn|hn := lt_trichotomy n 2
      · interval_cases n <;> contradiction
      · assumption
      · have : 3 < (n + 1) * n / 2 := by
          calc
            _ = (2 + 1) * 2 / 2 := by rfl
            _ < _ := by
              refine div_lt_div_of_lt_of_dvd ?_ ?_
              · have : n % 2 < 2 := mod_lt _ (by norm_num)
                apply dvd_of_mod_eq_zero
                rw [mul_mod, add_mod, one_mod]
                interval_cases n % 2 <;> norm_num
              · gcongr
        linarith only [this, h]
    | m + 1 =>
      -- Let us show the following auxiliary statement:
      have haux : 25 ^ (m + 1) % 10 = 5 := by
        clear h
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ, mul_mod, ih]
      -- Thus, the expression on the right is `7` modulo `10`
      have h1 : (25 ^ (m + 1) + 2) % 10 = 7 := by
        rw [add_mod, haux]
      -- On the other hand, the left hand side is never `7` modulo `10`
      have h2 : (n + 1) * n / 2 % 10 ≠ 7 := by
        have : n % 20 < 20 := mod_lt _ (by norm_num)
        rw [← mod_mul_right_div_self, mul_mod, add_mod n _, one_mod]
        rw [show 2 * 10 = 20 by rfl]
        interval_cases n % 20 <;> norm_num
      -- Thus both sides can never be equal
      simp at h
      have : (n + 1) * n / 2 % 10 = (25 ^ (m + 1) + 2) % 10 := by congr
      rw [h1] at this
      exact False.elim <| h2 this
  · -- `(2, 0)` is a solution
    intro h
    simp at h
    rw [h.1, h.2]
    rfl
