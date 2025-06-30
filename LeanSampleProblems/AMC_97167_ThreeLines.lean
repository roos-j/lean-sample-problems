import Mathlib

/- Which of these describes the graph of $x^2*(x+y+1)=y^2*(x+y+1)$ ?

(A) two parallel lines
(B) two intersecting lines
(C) three lines that all pass through a common point
(D) three lines that do not all pass through a common point
(E) a line and a parabola -/
theorem algebra_97167 {x y : ℝ} (h : x ^ 2 * (x + y + 1) = y ^ 2 * (x + y + 1)) :
    (y = x ∨ y = -x ∨ x + y + 1 = 0) ∧ (∀ x : ℝ, ¬ ∃ y, y = x ∧ y = -x ∧ x + y + 1 = 0)  := by
  -- We show that `(x, y)` must lie on one of the three lines
  constructor
  focus {
    -- If `x + y + 1 ≠ 0`, then we must have `y^2 = x^2` and this implies `y = x` or `y = -x`
    by_cases h' : x + y + 1 = 0
    · right; right; exact h'
    · have e : y ^ 2 = x ^2 := (mul_right_cancel₀ h' h).symm
      rw [← or_assoc]; left
      exact sq_eq_sq_iff_eq_or_eq_neg.mp e
  }
  -- It remains to show that the three lines do not all pass through a common point
  -- This is because the lines `y = x` and `y = -x` intersect in `(0, 0)` and this point does not lie on the line `x + y + 1 = 0`
  intro x
  by_contra h
  obtain ⟨y, h1, h2, h3⟩ := h
  have ip : x = 0 ∧ y = 0 := by constructor <;> linarith only [h1, h2]
  rw [ip.1, ip.2] at h3
  linarith only [h3]
