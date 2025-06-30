import Mathlib

open Real

/- Let $a, b, c$ be positive real numbers with $a b c=1$. Show that
$$\frac{1+a}{1+a+a b}+\frac{1+b}{1+b+b c}+\frac{1+c}{1+c+c a} = 2.$$
-/
theorem inequalities_262438 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) : (1 + a) / (1 + a + a * b) + (1 + b) / (1 + b + b * c) +
      (1 + c) / (1 + c + c * a) = 2 := by
  -- Let us calculate by using the assumption that `abc = 1`:
  calc
    _ = (1 + a) / (1 + a + a * b) + a * (1 + b) / (a * (1 + b + b * c)) +
      a * b * (1 + c) / (a * b * (1 + c + c * a)) := by field_simp; ring
    _ = (1 + a) / (1 + a + a * b) + (a + a * b) / (a + a * b + a * b * c) +
      (a * b + a * b * c) / (a * b + a * b * c + a * b * c * a) := by congr <;> ring
    _ = (1 + a) / (1 + a + a * b) + (a + a * b) / (1 + a + a * b) +
      (a * b + 1) / (1 + a + a * b) := by rw [habc]; field_simp; ring
    _ = _ := by field_simp; ring
