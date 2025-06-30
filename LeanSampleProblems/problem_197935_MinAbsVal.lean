import Mathlib

/- Find the smallest possible value of $\left|2015 m^{5}-2014 n^{4}\right|$, given that $m, n$ are natural numbers. -/
theorem number_theory_197935 :
    IsLeast {x : ℤ | ∃ m n : ℕ, x = |(2015 * m ^ 5 : ℤ) - 2014 * n ^ 4|} 0 := by
  constructor
  · -- By inspection one sees that `m = 2014 * 2015 ^ 3` and `n = 2014 * 2015 ^ 4` works
    use 2014 * 2015 ^ 3, 2014 * 2015 ^ 4
    norm_num
  · -- `0` is smallest possible because absolute values are nonnegative
    rintro x ⟨_, _, h⟩
    rw [h]; exact abs_nonneg _
