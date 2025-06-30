import Mathlib

/- Leah has 13 coins, all of which are pennies and nickels.
  If she had one more nickel than she has now, then she would have the same number of pennies and nickels. In cents, how much are Leah's coins worth?
(A) 33
(B) 35
(C) 37
(D) 39
(E) 41
 -/
theorem algebra_96204 {p n : ℕ} (hp : p + n = 13) (hn : n + 1 = p) :
    p * 1 + n * 5 = 37 := by
  -- Since `n + 1 = p` and `p + n = 13`, we must have:
  have : 2 * n + 1 = 13 := by rwa [← hn, add_assoc, add_comm 1, ← add_assoc, ← two_mul] at hp
  -- Thus `n = 6` and `p = 7`
  have n_eq : n = 6 := by linarith
  have p_eq : p = 7 := by rw [n_eq] at hn; exact hn.symm
  -- And the total value is `37`
  rw [n_eq, p_eq]
