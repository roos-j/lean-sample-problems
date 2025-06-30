import Mathlib

open Real

/- Let $a, b>0$, and $a b>2007 a+2008 b$, prove the inequality: $a+b>(\sqrt{2007}+\sqrt{2008})^{2}$. -/
theorem inequalities_113985 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b > 2007 * a + 2008 * b) :
    a + b > (√2007 + √2008)^2 := by
  -- We first show the required version of `AM-GM`
  have amgm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x + y ≥ 2 * √(x * y) := by
    apply le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, sq_sqrt (by positivity)]
    linarith only [show 0 ≤ (x - y) ^ 2 by exact sq_nonneg _]

  -- Multiplying our inequality by `(a + b) / (a * b)` on both sides gives
  have e1 : a + b > 2007 * (a + b) / b + 2008 * (a + b) / a := by
    calc
      _ = (a * b) * (a + b) / (a * b) := by field_simp
      _ > (2007 * a + 2008 * b) * (a + b) / (a * b) := by gcongr
      _ = _ := by field_simp; ring
  -- Then we can calculate using AM-GM:
  calc
    _ > 2007 * (a + b) / b + 2008 * (a + b) / a := e1
    _ = 2007 + (2007 * a / b + 2008 * b / a) + 2008 := by field_simp; ring
    _ ≥ 2007 + 2 * √((2007 * a / b) * (2008 * b / a)) + 2008 := by gcongr; exact amgm _ _ (by positivity) (by positivity)
    _ = 2007 + 2 * √(2007 * 2008) + 2008 := by congr! 4; field_simp; ring
    _ = _ := by rw [add_pow_two, sqrt_mul (by positivity), sq_sqrt (by positivity), sq_sqrt (by positivity)]; ring
