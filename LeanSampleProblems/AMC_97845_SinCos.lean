import Mathlib

open Real

/- The functions $\sin⁡(x)$ and $\cos⁡(x)$ are periodic with least period $2\pi$.
What is the least period of the function $\cos⁡(\sin⁡(x))$ ?
(A) $\pi/2$
(B) $\pi$
(C) $2\pi$
(D) $4\pi$
(E) The function is not periodic. -/
theorem algebra_97845 {f : ℝ → ℝ} (hf : f = fun x ↦ cos (sin x)) :
    (∃ x, f (x + π / 2) ≠ f x) ∧ ∀ x, f (x + π) = f x := by
  -- We first show that `f` is not `π /2` periodic by giving a counterexample
  constructor
  · use π / 2
    rw [hf]
    have one_ne_cos_one : 1 ≠ cos 1 := by
      have one_lt_pi : 1 ≤ π := by
        calc
          _ ≤ 3 := by norm_num
          _ ≤ π := le_of_lt pi_gt_three
      nth_rewrite 1 [← cos_zero]
      by_contra h
      exact (show (0 : ℝ) ≠ 1 by norm_num) <| injOn_cos ⟨by rfl, pi_nonneg⟩ ⟨by norm_num, one_lt_pi⟩ h
    simp [one_ne_cos_one]
  -- Next we show that `f` is `π` periodic
  · intro x
    rw [hf]
    simp only [sin_add_pi, cos_neg]
