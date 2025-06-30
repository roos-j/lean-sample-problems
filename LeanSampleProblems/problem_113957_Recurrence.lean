import Mathlib

/- Find the general term of the sequence defined by $a_{0}=a_{1}=0, a_{n+2}=6 a_{n+1}-9 a_{n}+2^{n}+n$. -/
theorem algebra_113957 {a : ℕ → ℝ}
    (ha01 : a 0 = 0 ∧ a 1 = 0)
    (han : ∀ n, a (n + 2) = 6 * a (n + 1) - 9 * a n + 2 ^ n + n) :
    ∀ n, a n = (n + 1) / 4 + 2 ^ n + (-5 / 4 + 5 / 12 * n) * 3 ^ n := by
  /- Note: Part of the solution is implicit in providing the formula for `a n`.
    It remains only to show that the claimed formula is correct. -/
  intro n
  -- The claim follows by (strong) induction on `n`
  induction' n using Nat.strongRecOn with n ih
  match n with
  | 0 => simp [ha01.1]; norm_num
  | 1 => simp [ha01.2]; norm_num
  | n + 2 => -- Plugging in the inductive hypothesis and simplifying gives the claim
    rw [han, ih _ (by norm_num), ih _ (by norm_num)]
    push_cast
    ring
