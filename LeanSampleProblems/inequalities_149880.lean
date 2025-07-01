import Mathlib

namespace inequalities_149880

open Finset

/- Auxiliary inequality between rationals needed for the lower bound inductive step. -/
lemma l_auxl {n : ℕ} : (2 : ℝ) * (n + 1) / (3 * (n + 1) + 1) - 2 * n / (3 * n + 1) ≤ 1 / (2 * n + 1) + 1 / (2 * n + 1 + 1) - 1 / (n + 1) := by
  -- This follows by canceling denominators on both sides and comparing coefficients
  field_simp
  have hpos1 : 0 < ((3 : ℝ) * (n + 1) + 1) * (3 * n + 1) := by positivity
  have hpos2 : 0 < ((2 : ℝ) * n + 1) * (2 * n + 1 + 1) * (n + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hpos1
  refine le_of_mul_le_mul_left ?_ hpos2
  field_simp
  ring_nf
  gcongr <;> norm_num

/- Auxiliary inequality between rationals needed for the upper bound inductive step. -/
lemma l_auxr {n : ℕ} (hn : 1 ≤ n) : ((3 : ℝ) * n + 1) / (4 * n + 4) + (1 / (2 * n + 1) + 1 / (2 * n + 1 + 1) - 1 / (n + 1)) ≤ (3 * (n + 1) + 1) / (4 * (n + 1) + 4) := by
  -- This follows by canceling denominators on both sides and comparing coefficients
  -- We first need to write `n` as `n' + 1` because the claim is false for `n = 0`
  letI n' := n - 1
  rw [show n = n' + 1 by omega]
  field_simp
  have hpos1 : 0 < (((4 : ℝ) * (n' + 1) + 4) * ((2 * (n' + 1) + 1) * (2 * (n' + 1) + 1 + 1) * ((n' + 1) + 1))) := by positivity
  have hpos2 : 0 < ((4 : ℝ) * ((n' + 1) + 1) + 4) := by positivity
  refine le_of_mul_le_mul_left ?_ hpos1
  refine le_of_mul_le_mul_left ?_ hpos2
  field_simp
  ring_nf
  gcongr <;> norm_num

/- Auxiliary lemma that's not in mathlib -/
lemma l_sum_Ioc_succ_bot {a : ℕ → ℝ} {n m : ℕ} (hnm : n + 1 ≤ m) :
    ∑ k in Ioc (n + 1) m, a k = ∑ k in Ioc n m, a k - a (n + 1) := by
  have := sum_Ioc_add_eq_sum_Icc (a := n + 1) (b := m) (f := a) hnm
  rw [← sum_Ico_add_eq_sum_Icc (by omega)] at this
  have := sum_eq_sum_Ico_succ_bot (a := n) (b := m) (f := a) (by omega)
  have := sum_Ioc_add_eq_sum_Icc (a := n) (b := m) (f := a) (by omega)
  rw [← sum_Ico_add_eq_sum_Icc (by omega)] at this
  linarith

/-
  14th Irish 2001
  Problem A4

  Show that 2n/(3n+1) ≤ ∑ n< k ≤ 2n, 1/k ≤ (3n+1)/(4n+4).
-/
theorem inequalities_149880 (n : ℕ) :
  (2 * n / (3 * n + 1 : ℝ)) ≤ ∑ k ∈ Ioc n (2 * n), (1 / k : ℝ) ∧
    ∑ k ∈ Ioc n (2 * n), (1 / k : ℝ) ≤ ((3 * n + 1) / (4 * n + 4)) := by
  -- We proceed by induction on `n`
  induction' n with n ih
  · -- For `n = 0` there is nothing to show.
    simp
  · by_cases hn : n = 0
    · -- Verify `n = 1` by direct computation
      simp [hn]
      norm_num
    · -- It remains to show that if the claim holds for some `n ≥ 1`, then it holds for `n + 1`
      -- This follows since the difference between terms on both sides is controlled by `l_auxl`, `l_auxr`
      have hn : 1 ≤ n := by omega
      obtain ⟨ihl, ihr⟩ := ih
      constructor
      · -- We verify the left-hand side inequality first
        rw [mul_add, show 2 * 1 = 1 + 1 by norm_num, ← add_assoc]
        rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega)]
        rw [l_sum_Ioc_succ_bot (by omega)]
        calc
          _ = (2 : ℝ) * n / (3 * n + 1) + (2 * (n + 1) / (3 * (n + 1) + 1) - 2 * n / (3 * n + 1)) := by
            field_simp
            ring
          _ ≤ ∑ k ∈ Ioc n (2 * n), (1 / k : ℝ) + (2 * (n + 1) / (3 * (n + 1) + 1) - 2 * n / (3 * n + 1)) := by
            gcongr
          _ ≤ ∑ k ∈ Ioc n (2 * n), (1 / k : ℝ) + (1 / ↑(2 * n + 1) + 1 / ↑(2 * n + 1 + 1) - 1 / ↑(n + 1)) := by
            gcongr ?_ + ?_
            · rfl
            · exact_mod_cast l_auxl
          _ = _ := by
            field_simp
            ring
      · -- The right-hand side inequality is analogous
        rw [mul_add, show 2 * 1 = 1 + 1 by norm_num, ← add_assoc]
        rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega)]
        rw [l_sum_Ioc_succ_bot (by omega)]
        calc
          _ = ∑ k ∈ Ioc n (2 * n), (1 / k : ℝ) + (1 / ↑(2 * n + 1) + 1 / ↑(2 * n + 1 + 1) - 1 / ↑(n + 1)) := by
            field_simp
            ring
          _ ≤ (3 * n + 1) / (4 * n + 4) + (1 / (2 * n + 1) + 1 / (2 * n + 1 + 1) - 1 / (n + 1)) := by
            push_cast
            gcongr
          _ ≤ _ := by
            exact_mod_cast l_auxr hn

end inequalities_149880
