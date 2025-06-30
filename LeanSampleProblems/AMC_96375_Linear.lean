import Mathlib

/- Randy drove the first third of his trip on a gravel road, the next 20 miles on pavement,
  and the remaining one-fifth on a dirt road. In miles, how long was Randy's trip?
  (A) 30
  (B) 400/11
  (C) 75/2
  (D) 40
  (E) 300/7
​ -/
theorem algebra_96375 (x : ℝ) (h₁ : (x / 3) + 20 + (x / 5) = x) :
    x = 300 / 7 := by
  -- Solving the linear equation gives the claim.
  linarith
