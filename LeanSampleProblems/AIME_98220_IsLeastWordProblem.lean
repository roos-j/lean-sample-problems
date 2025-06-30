import Mathlib

open Finset

/- The members of a distinguished committee were choosing a president,
  and each member gave one vote to one of the 27 candidates.
  For each candidate, the exact percentage of votes the candidate got was smaller by at least 1
  than the number of votes for that candidate.
  What was the smallest possible number of members of the committee? -/
theorem number_theory_98220 : IsLeast { s | ∃ v : Fin 27 → ℕ, 0 < s ∧ s = ∑ i, v i ∧ ∀ i, ((v i) : ℝ) * 100 / s + 1 ≤ v i} 134 := by
  -- We need to show that 134 is possible and that 134 is minimal
  constructor
  · -- To show that 134 is possible we just need to give an example of `v`
    set v : Fin 27 → ℕ := fun i ↦ if i = 0 then 4 else 5 with v_def
    use v
    constructorm* _ ∧ _
    · norm_num
    · rw [v_def]; decide
    · intro i; rw [v_def]
      fin_cases i <;> { simp; norm_num }
  · -- It remains to show that 134 is a lower bound of all possible s
    rintro s ⟨v, hs, hs', hv⟩
    -- First observe that `v i ≥ 2`
    have two_le : ∀ i, 2 ≤ v i := by
      by_contra h; push_neg at h
      obtain ⟨i, hi⟩ := h
      specialize hv i
      interval_cases v i
      · norm_num at hv
      · norm_num at hv
        suffices (100 : ℝ) ≤ 0 by norm_num at this
        calc
          _ = (100 : ℝ) / s * s := by rw [div_mul_cancel₀]; norm_cast; exact (ne_of_lt hs).symm
          _ ≤ 0 * s := by gcongr
          _ = 0 := zero_mul _
    -- This implies the following lower bound for `s`
    have le_s : ∀ i, ((v i) : ℝ) * 100 / (v i - 1) ≤ s := by
      intro i
      have : 0 < ((v i) : ℝ) - 1 := by simp; linarith only [two_le i]
      specialize hv i
      calc
        _ = (((v i) : ℝ) * 100 / s + 1 - 1) * (s / (((v i) : ℝ) - 1)) := by field_simp
        _ ≤ (((v i) : ℝ) - 1) * (s / (((v i) : ℝ) - 1)) := by gcongr
        _ = _ := by field_simp
    -- Now suppose `s < 134`
    by_contra h; push_neg at h
    -- Then there must exist `i` with `v i < 5`
    have : ∃ i, v i < 5 := by
      -- Because if not then `v i ≥ 5` for all `i` which implies `s ≥ 135`, contradiction
      by_contra h'
      push_neg at h'
      suffices le_s' : 135 ≤ s by linarith only [h, le_s']
      calc
        _ = ∑ i : Fin 27, 5 := by rw [sum_const]; rfl
        _ ≤ ∑ i : Fin 27, v i := by apply sum_le_sum; exact fun i _ ↦ h' i
        _ = s := by rw [hs']
    obtain ⟨i, lt_five⟩ := this
    specialize two_le i
    specialize le_s i
    -- It remains to rule out the possibility that one of the `v i` can be `2`, `3` or `4`, but this follows from `le_s`
    interval_cases v i
    · norm_num at le_s
      linarith only [le_s, h]
    · norm_num at le_s
      linarith only [le_s, h]
    · have : 133 < s := by
        suffices 133 < (s : ℝ) by norm_cast at this
        norm_num at le_s
        linarith only [le_s]
      linarith only [this, h]
