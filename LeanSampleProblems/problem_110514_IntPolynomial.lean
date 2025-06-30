import Mathlib

/- Let $f(x)=x^{3}+a x^{2}+b x+c$, where $a, b$ and $c$ are distinct non-zero integers.
For which $a, b$ and $c$ do the equalities $f(a)=a^{3}$ and $f(b)=b^{3}$ hold? -/
theorem algebra_110514 {a b c : ℤ} {f : ℤ → ℤ} (ha : a ≠ 0) -- (hb : b ≠ 0) (hc : c ≠ 0)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hf : ∀ x, f x = x^3 + a * x^2 + b * x + c)
    (h1 : f a = a^3) (h2 : f b = b^3) : a = -2 ∧ b = 4 ∧ c = 16 := by
  -- The assumptions `hb`, `hc` are not needed.
  -- By assumption `a, b` satisfy the following equations
  have e1 : a ^ 3 + a * b + c = 0 := by rw [hf] at h1; linarith only [h1]
  have e2 : a * b ^ 2 + b ^ 2 + c = 0 := by rw [hf] at h2; linarith only [h2]

  -- Subtracting one from the other we get
  have e3 : (a + 1) * b ^ 2 - a * b - a ^ 3 = 0 := by linear_combination e2 - e1

  -- Factoring and using `a ≠ b` we get that
  have e4 : (a + 1) * b + a ^ 2 = 0 := by
    have : (b - a) * ((a + 1) * b + a ^ 2) = 0 := by rw [← e3]; ring
    exact (mul_eq_zero_iff_left (show b - a ≠ 0 by omega)).mp this

  -- Thus, `a ^ 2` is divisible by `a + 1`
  have h2 : a + 1 ∣ a ^ 2 := by use -b; linarith only [e4]

  -- Since `a ^ 2`, `a + 1` are coprime, we must have `a + 1 = 1` or `a + 1 = -1`
  have h3 : a + 1 = 1 ∨ a + 1 = -1 := Int.isUnit_iff.mp <| IsCoprime.isUnit_of_dvd (by use 1 - a, 1; ring) h2

  -- The first case gives `a = 0` (contradiction) and the second gives the solution
  obtain h | h := h3
  · exact False.elim <| ha (by omega)
  · have a_eq : a = -2 := by omega
    have b_eq : b = 4 := by rw [a_eq] at e4; omega
    exact ⟨a_eq, b_eq, by rw [a_eq, b_eq] at e1; omega⟩
