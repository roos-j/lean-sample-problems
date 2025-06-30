import Mathlib

open Nat

/- The six-digit number 2​0​2​1​0​A​ is prime for only one digit A. What is A?
  (A) 1
  (B) 3
  (C) 5
  (D) 7
  (E) 9 -/
theorem number_theory_93179 : ¬ Nat.Prime (202101) ∧ ¬ Nat.Prime (202103) ∧ ¬ Nat.Prime (202105)
    ∧ ¬ Nat.Prime (202107) := by
  -- 202101 is not prime because it is divisible by 3
  have not1 : ¬ Nat.Prime (202101) := by
    apply not_prime_of_dvd_of_lt (m := 3) <;> norm_num
  -- 202103 is not prime because it is divisible by 11
  have not3 : ¬ Nat.Prime (202103) := by
    apply not_prime_of_dvd_of_lt (m := 11) <;> norm_num
  -- 202105 is not prime because it is divisible by 5
  have not5 : ¬ Nat.Prime (202105) := by
    apply not_prime_of_dvd_of_lt (m := 5) <;> norm_num
  -- 202107 is not prime because it is divisible by 3
  have not7 : ¬ Nat.Prime (202107) := by
    apply not_prime_of_dvd_of_lt (m := 3) <;> norm_num
  exact ⟨not1, not3, not5, not7⟩
