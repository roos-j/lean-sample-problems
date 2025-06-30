import Mathlib

open Real intervalIntegral Set

/- Needed for the verification of function properties later -/
lemma l_subset_aux {x : ℝ} (hx : 0 < x) : uIcc 1 x ⊆ Ioi 0 := by
  intro y hy
  obtain ⟨hy, _⟩ := hy
  simp only [inf_le_iff] at hy
  apply mem_Ioi.mpr
  obtain hy | hy := hy
  · positivity
  · exact Trans.trans hx hy

/- Example 9

  Let $f(x): \mathbf{R}^{+} \rightarrow \mathbf{R}^{+}$,

  solve the functional inequality $f^{\prime}(x)(x-1)>0$.
 -/
theorem calculus_284337 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Ioi 0))
    (hf' : ContinuousOn (deriv f) (Ioi 0))
    (h : ∀ x > 0, deriv f x * (x - 1) > 0) :
    ∃ p : ℝ → ℝ, (∀ x > 0, p x > 0) ∧ (∀ x > 0, f x = f 1 + ∫ y in (1)..x, p y / (y - 1)) := by
  -- Let `p x = f' x * (x - 1)
  use fun x ↦ deriv f x * (x - 1)
  refine  ⟨h, fun x hx ↦ ?_⟩
  -- Then we use the fundamental theorem of calculus
  calc
    _ = f 1 + ∫ y in (1)..x, deriv f y := by
      rw [integral_deriv_eq_sub]
      · ring
      · intro y hy
        replace hy := l_subset_aux hx hy
        apply hf.differentiableAt (x := y)
        exact Ioi_mem_nhds hy
      · apply ContinuousOn.intervalIntegrable
        intro y hy
        specialize hf' y (l_subset_aux hx hy)
        exact hf'.mono (l_subset_aux hx)
    _ = _ := by
      congr! 1
      apply integral_congr_ae
      apply MeasureTheory.ae_iff.mpr
      apply le_antisymm ?_ (by positivity)
      calc
        _ ≤ MeasureTheory.volume {(1 : ℝ)} := by
          apply MeasureTheory.measure_mono
          apply Set.compl_subset_compl.mp
          intro x hx
          simp only [Classical.not_imp, mem_compl_iff, mem_setOf_eq, not_and,
            Decidable.not_not]
          intro hx'
          have : x - 1 ≠ 0 := by
            simp only [mem_compl_iff, mem_singleton_iff] at hx
            exact sub_ne_zero_of_ne hx
          field_simp
        _ = 0 := volume_singleton
