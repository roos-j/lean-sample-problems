import Mathlib

/- Show that 8 numbers be chosen from the first hundred natural numbers so that their sum is divisible by each of them. -/
theorem number_theory_233446 :
    ∃ s : Finset ℕ, s.card = 8 ∧ ∀ n ∈ s, n ≤ 100 ∧ ∑ i ∈ s, i ≡ 0 [MOD n] := by
  -- There are many such sets that can be found by trial and error. Here is one example:
  let s : Finset ℕ := {1, 2, 3, 6, 12, 24, 48, 96}
  use s
  -- Note: From here the claim can be shown by `decide`, but we provide some more human details.
  -- The sum of the numbers is `192`
  have h : ∑ i ∈ s, i = 192 := by rfl
  and_intros
  · rfl -- There are 8 numbers
  · intro n hn
    rw [h]
    -- Each of the numbers is `≤ 100` and `192` is divisible by each of the numbers
    fin_cases hn <;> {
      constructor
      · norm_num
      · rfl
    }
