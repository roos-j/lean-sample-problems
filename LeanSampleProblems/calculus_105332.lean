import Mathlib

open Real intervalIntegral Set

/- Problem 4

Determine the differentiable function $f:(0, \infty) \rightarrow \mathbf{R}$ knowing that $f^{\prime}(x)=f(x)+\frac{f(x)}{x}+e^{x}$, for any $x>0$ and $f(1)=e$.

Gazeta Matematica

Selected by: Astalus Niculina, Ilie Stefan, Matefi Istvan

INSPECTORATUL SCOLAR JUDETEAN MURES

S.S.M.R - BRANCH MURES

Mathematics Olympiad

Local phase -/
theorem calculus_105332 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Ioi 0))
  (h : ∀ x > 0, deriv f x = f x + f x / x + exp x) (h1 : f 1 = exp 1) :
    ∀ x > 0, f x = (1 + log x) * x * exp x := by
  -- The key is to define a function `g` as follows
  letI g : ℝ → ℝ := fun x ↦ (f x) / (x * exp x) - log x
  -- Then `g` is differentiable on (0, ∞) with derivative equal to `0`
  have hg {x : ℝ} (hx : 0 < x) : HasDerivAt g 0 x := by
    convert HasDerivAt.sub (.div (hf.hasDerivAt _) (.mul (hasDerivAt_id _)
        (hasDerivAt_exp _)) ?_) (hasDerivAt_log ?_) using 1
    · field_simp [h x hx]
      ring
    · exact Ioi_mem_nhds hx
    · positivity
    · positivity
  -- Also, `g 1 = 1`
  have hg1 : g 1 = 1 := by
    simp [g, h1]
  -- Therefore `g x = 1` for all `0 < x`
  have g_eq {x : ℝ} (hx : 0 < x) : g x = 1 := by
    rw [← hg1]
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (s := Ioi 0)
    · exact convex_Ioi _
    · intro y hy
      exact DifferentiableAt.differentiableWithinAt (hg hy).differentiableAt
    · intro y hy
      simp only [mem_Ioi] at hy
      convert ((hg hy).hasFDerivAt.hasFDerivWithinAt (s := Ioi 0)).fderivWithin ?_
      · ext
        simp
      · refine UniqueDiffOn.uniqueDiffWithinAt ?_ hy
        exact uniqueDiffOn_Ioi 0
    · exact hx
    · norm_num
  -- Substituting the definition of `g`, the claim follows
  intro x hx
  specialize g_eq hx
  field_simp [g] at g_eq
  linarith only [g_eq]
