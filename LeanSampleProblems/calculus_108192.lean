import Mathlib

namespace calculus_108192

def f (a : Fin 3 → ℝ) : ℝ → ℝ := fun x ↦ a 2 * x ^ 2 + a 1 * x + a 0

/- Compute the first derivative -/
lemma l_hasDerivAt_f {a : Fin 3 → ℝ} {x : ℝ} : HasDerivAt (f a) (2 * a 2 * x + a 1) x := by
  convert HasDerivAt.add (.add (.const_mul (a 2) (hasDerivAt_pow _ _)) (.const_mul (a 1) (hasDerivAt_id _))) (hasDerivAt_const _ _) using 1
  ring

/- Compute the second derivative -/
lemma l_hasDerivAt_deriv_f {a : Fin 3 → ℝ} {x : ℝ} : HasDerivAt (deriv (f a)) (2 * a 2) x := by
  have : deriv (f a) = fun x ↦ 2 * a 2 * x + a 1 := by
    ext
    exact HasDerivAt.deriv l_hasDerivAt_f
  rw [this]
  convert HasDerivAt.add (.const_mul (2 * a 2) (hasDerivAt_id _)) (hasDerivAt_const _ _) using 1
  ring

/-
Given the function $f(x)=a_{2} x^{2}+a_{1} x+a_{0}$ with coefficients $a_{0}, a_{1}, a_{2} \in \mathbb{R}$,
show that a primitive of the function $\frac{f(x)-f(k)}{x-k}$, where $k$ is a real constant, is
$$
F(x)=\frac{1}{2}\left(f(x)+a_{1} x+a_{0}\right)+k\left(f^{\prime}(x)-a_{2} x-a_{1}\right)
$$

Mathematical Gazette 1956 -/
theorem calculus_108192 {a : Fin 3 → ℝ} {k : ℝ} {F : ℝ → ℝ} (hF : ∀ x, F x = (f a x + a 1 * x + a 0) / 2 + k * (deriv (f a) x - a 2 * x - a 1)) : ∀ x ≠ k, deriv F x = ((f a) x - (f a) k) / (x - k)  := by
  -- Let `x ≠ k`
  intro x hx
  -- We verify the identity by computing both sides.
  have deriv_F : deriv F x = (a 2) * (x + k) + a 1 := by
    apply HasDerivAt.deriv
    rw [show F = fun x ↦ (f a x + a 1 * x + a 0) / 2 + k * (deriv (f a) x - a 2 * x - a 1) by ext; rw [hF]]
    convert HasDerivAt.add (.div_const (.add (.add l_hasDerivAt_f (.const_mul (a 1) (hasDerivAt_id _))) (hasDerivAt_const _ _)) 2)
      (.const_mul k (.sub (.sub (l_hasDerivAt_deriv_f) (.const_mul (a 2) (hasDerivAt_id _))) (hasDerivAt_const _ _))) using 1
    ring
  rw [deriv_F, f, f]
  have := sub_ne_zero_of_ne hx
  field_simp
  ring

end calculus_108192
