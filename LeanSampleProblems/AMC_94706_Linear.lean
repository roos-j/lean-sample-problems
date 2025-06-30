import Mathlib

/- The players on a basketball team made some three-point shots, some two-point shots, and some one-point free throws.
They scored as many points with two-point shots as with three-point shots.
Their number of successful free throws was one more than their number of successful two-point shots.
The team's total score was 61 points. How many free throws did they make?

(A) 13
(B) 14
(C) 15
(D) 16
(E) 17
-/
theorem algebra_94706 (x y z : ℕ) (h₀ : x * 2 = y * 3) (h₁ : z = x + 1) (h₂ : x * 2 + y * 3 + z = 61) :
    z = 13 := by
  -- Substituting the second into the third equation gives
  have : x * 3 + y * 3 = 60 := by rw [h₁] at h₂; linarith only [h₂]
  -- Plugging in the first equation gives
  have : x * 5 = 60 := by rwa [← h₀, ← mul_add] at this
  -- This gives `x = 12` and thus `z = 13`
  rw [h₁]; rw [show x = 12 by linarith only [this]]
