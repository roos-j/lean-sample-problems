import Mathlib

/- First we record two auxiliary lemmas -/
lemma l_aux1 {x : ℝ} (hx : x ≠ 0 ∧ x ≠ 1) : 1 / (1 - x) ≠ 0 ∧ 1 / (1 - x) ≠ 1 := by
  have : 1 - x ≠ 0 := sub_ne_zero_of_ne hx.2.symm
  constructor
  · positivity
  · simp [hx.1]

lemma l_aux2 {x : ℝ} (hx : x ≠ 0 ∧ x ≠ 1) : (x - 1) / x ≠ 0 ∧ (x - 1) / x ≠ 1 := by
  have : x - 1 ≠ 0 := sub_ne_zero_of_ne hx.2
  have := hx.1
  constructor
  · positivity
  · field_simp

/- Let's determine all functions $f: \mathbb{R} \backslash\{0,1\} \rightarrow \mathbb{R}$ that satisfy the equation

$$f\left(\frac{x-1}{x}\right)+f\left(\frac{1}{1-x}\right)=2-2 x$$
 -/
theorem algebra_209238 (f : ℝ → ℝ) : (∀ x, x ≠ 0 ∧ x ≠ 1 → f ((x - 1) / x) + f (1 / (1 - x)) = 2 - 2 * x) ↔
    ∀ x, x ≠ 0 ∧ x ≠ 1 → f x = x + 1 / x + 1 / (x - 1) := by
  constructor
  · -- We first show that the functional equation implies that `f` is the claimed function
    rintro h x ⟨hx0, hx1⟩
    have : x - 1 ≠ 0 := sub_ne_zero_of_ne hx1
    have : 1 - x ≠ 0 := sub_ne_zero_of_ne hx1.symm

    -- Substituting `x ↦ 1 / (1 - x)` in the functional equation gives:
    have h2 : f x + f ((x - 1) / x) = 2 - 2 * 1 / (1 - x) := by
      have := h (1 / (1 - x)) <| l_aux1 ⟨hx0, hx1⟩
      field_simp at this
      ring_nf at this
      field_simp
      ring_nf
      assumption

    -- Substituting `x ↦ (x - 1) / x` in the functional equation gives:
    have h3 : f (1 / (1 - x)) + f x = 2 - 2 * (x - 1) / x := by
      have : -1 + x ≠ 0 := by rw [add_comm]; assumption
      have := h ((x - 1) / x) <| l_aux2 ⟨hx0, hx1⟩
      field_simp at this
      ring_nf at this
      field_simp
      ring_nf
      rw [show (1 - x)⁻¹ = -(-1 + x)⁻¹ by field_simp; ring]
      assumption

    specialize h x ⟨hx0, hx1⟩
    -- Now we can solve for `f x` by adding `h2`, `h3` and subtracting `h`:
    calc
      _ = 1 / 2 * ((f x + f ((x - 1) / x)) + (f (1 / (1 - x)) + f x) - (f ((x - 1) / x) + f (1 / (1 - x)))) := by ring
      _ = _ := by
        rw [h2, h3, h]
        field_simp
        ring
  · -- It remains to show that the claimed function solves the functional equation
    rintro h x ⟨hx0, hx1⟩
    have : x - 1 ≠ 0 := sub_ne_zero_of_ne hx1
    have : 1 - x ≠ 0 := sub_ne_zero_of_ne hx1.symm
    have h2 := h (1 / (1 - x)) <| l_aux1 ⟨hx0, hx1⟩
    have h3 := h ((x - 1) / x) <| l_aux2 ⟨hx0, hx1⟩
    rw [h2, h3]
    field_simp
    ring
