import Mathlib

open Set Real intervalIntegral

/-
Let $a$ be a constant, $0 < a \neq 1$.
Find all $C^1$ functions $f: \mathrm{R}^{+} \rightarrow \mathrm{R}$,
such that for any $\mathrm{x}, \mathrm{y} \in \mathrm{R}^{+}, f(\mathrm{xy})=f(\mathrm{x})+f(\mathrm{y})$ and $f(a)=1$.
-/
theorem algebra_175543 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ioi 0))
    (h : ∀ x y, 0 < x → 0 < y → f (x * y) = f x + f y) (h' : f a = 1) :
    ∀ x, 0 < x → f x = logb a x := by
  -- Comment: The assumption `hf` could be weakened substantially, but some assumption is needed.
  have := ha.1
  -- Taking `x = y = 1` we get:
  have f_one : f 1 = 0 := by
    have := h 1 1 (by norm_num) (by norm_num)
    simpa
  let f' := deriv f
  -- By assumption, `f` is differentiable
  have hf' {x : ℝ} (hx : 0 < x) : HasDerivAt f (f' x) x := by
    simp only [hasDerivAt_deriv_iff, f']
    exact hf.differentiableOn (by rfl) |>.differentiableAt <| Ioi_mem_nhds hx
  let C₁ := f' 1
  -- By using the functional equation we will further show that:
  have deriv_f {x : ℝ} (hx : 0 < x) : f' x = C₁ * x⁻¹ := by
    -- By differentiating the functional equation wrt. `x` we obtain:
    have (y : ℝ) (hy : 0 < y) : f' x = y * f' (x * y) := by
      calc
        _ = deriv (fun x ↦ f x + f y) x := by simp
        _ = deriv (fun x ↦ f (x * y)) x := by
          apply Filter.EventuallyEq.deriv_eq
          refine Filter.mem_of_superset (x := Ioi 0) ?_ ?_
          · exact (IsOpen.mem_nhds_iff isOpen_Ioi).mpr hx
          · intro x hx; exact (h x y hx hy).symm
        _ = _ := by
          apply HasDerivAt.deriv
          convert HasDerivAt.comp x (hf' ?_) (hasDerivAt_mul_const y) using 1
          · exact mul_comm _ _
          · positivity
    -- Applying this with `y = 1 / x` gives the claim
    specialize this (1 / x) (by positivity)
    field_simp at this
    field_simp
    assumption
  -- Auxiliary lemma
  have uIcc_subset {x : ℝ} (hx : 0 < x) : uIcc 1 x ⊆ Ioi 0 := by
    intro _ h'
    simp only [mem_Ioi]
    obtain ⟨h', _⟩ := h'
    simp only [inf_le_iff] at h'
    rcases h' <;> linarith
  -- By the fundamental theorem of calculus this implies
  have f_eq {x : ℝ} (hx : 0 < x) : f x = C₁ * log x := by
    calc
      _ = f x - f 1 := by rw [f_one]; simp
      _ = ∫ y in (1 : ℝ)..x, f' y := by
        convert (integral_deriv_eq_sub ?_ ?_).symm
        · infer_instance
        · intro y hy
          exact hf.differentiableOn (by rfl) |>.differentiableAt <| Ioi_mem_nhds (uIcc_subset hx hy)
        · apply ContinuousOn.intervalIntegrable
          have := hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by rfl)
          apply this.mono
          exact uIcc_subset hx
      _ = ∫ y in (1 : ℝ)..x, C₁ * y⁻¹ := integral_congr <| fun _ hy ↦ deriv_f <| uIcc_subset hx hy
      _ = _ := by
        rw [integral_const_mul, integral_inv_of_pos (by positivity) (by positivity)]; simp
  -- Finally, we can plug in `x = a` to determine the value of `C₁`:
  have C₁_eq : C₁ = 1 / log a := by
    have := f_eq ha.1
    rw [h'] at this
    have pos : log a ≠ 0 := by
      apply log_ne_zero.mpr
      and_intros
      · positivity
      · exact ha.2
      · linarith only [ha.1]
    field_simp
    exact this.symm
  -- Then we have the claim:
  intro x hx
  rw [f_eq hx, C₁_eq, logb]
  field_simp
