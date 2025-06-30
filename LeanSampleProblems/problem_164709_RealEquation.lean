import Mathlib

open Real Function

/- The solution to the equation $2^{x^{2}-2 x}+3^{x^{2}-2 x}+x^{2}-2 x+\frac{1}{6}=0$ is $x=1$. -/
theorem algebra_164709 {x : ℝ} (h : 2^(x^2 - 2 * x) + 3^(x^2 - 2 * x) + x^2 - 2 * x + 1 / 6 = 0) : x = 1 := by
  -- Define an auxiliary function
  let f : ℝ → ℝ := fun t ↦ 2 ^ t + 3 ^ t + t
  -- From the original equation we have
  have e1 : f (x ^ 2 - 2 * x) = f (-1) := by simp only [f]; norm_num; linarith only [h]
  -- `f` is strictly increasing
  have f_incr : ∀ {x y : ℝ}, x < y → f x < f y := by
    intro x y hxy; simp only [f]; gcongr <;> simpa
  -- Thus `f` is injective
  have f_inj : Injective f := injective_of_increasing _ _ f f_incr
  -- This implies `x ^ 2 - 2 * x = -1`
  have : x ^ 2 - 2 * x = -1 := f_inj e1
  -- and this means that `x = 1`
  have : (x - 1) ^ 2 = 0 := by linarith only [this]
  simp at this
  linarith only [this]
