import Mathlib

/- Show that the only function $f: \mathbb{Z} \rightarrow \mathbb{R}$ such that $f(1)=\frac{5}{2}$ and

$$f(x) f(y)=f(x+y)+f(x-y), \text { for all } x, y \in \mathbb{Z}$$
is $f(x) = (2^{2x}+1)/2^x$.
 -/
theorem algebra_216927 {f : ℤ → ℝ} :
  (f 1 = 5 / 2 ∧ ∀ x y, f x * f y = f (x + y) + f (x - y))
    ↔ ∀ x, f x = (2 ^ (2 * x) + 1) / 2 ^ x := by
  -- We need to show both directions
  constructor
  · rintro ⟨hf1, hf⟩
    -- To show: `f` takes the specified form
    -- Let us first set `x = y = 0` to obtain:
    have hf0 : f 0 = 0 ∨ f 0 = 2 := by
      specialize hf 0 0
      rw [add_zero, sub_zero, ← two_mul] at hf
      by_cases hf0 : f 0 = 0
      · left; assumption
      · right
        exact mul_right_cancel₀ hf0 hf
    -- From setting `y = 1` we obtain the recursion:
    have hfrec : ∀ x, f (x + 1) = (5 / 2) * f x - f (x - 1) := by
      intro x
      specialize hf x 1
      rw [hf1] at hf
      linarith only [hf]
    obtain hf0|hf0 := hf0
    · -- Let `f 0 = 0`.
      -- Then we can compute the values of `f 2`, `f 3`, `f 4`
      have hf2 : f 2 = 25 / 4 := by linarith only [hfrec 1, hf0, hf1]
      have hf3 : f 3 = 105 / 8 := by linarith only [hfrec 2, hf1, hf2]
      have hf4 : f 4 = 425 / 16 := by linarith only [hfrec 3, hf2, hf3]
      -- Then setting `x = y = 2` we get a contradiction
      specialize hf 2 2
      simp at hf
      rw [← pow_two, hf2, hf4, hf0] at hf
      norm_num at hf
    · -- Let `f 0 = 2`.
      -- We first show that `f` is even.
      have hfeven : ∀ x, f (-x) = f x := by
        intro x
        -- This follows from comparing the original equation for `y` and `-y` with `x = 1`
        have h1 := hf 1 x
        have h2 := hf 1 (-x)
        rw [hf1] at h1
        rw [hf1] at h2
        rw [sub_neg_eq_add, ← sub_eq_add_neg] at h2
        linarith only [h1, h2]
      -- Thus it suffices to prove the claim for non-negative `x`.
      suffices h : ∀ x : ℕ, f x = (2 ^ (2 * x) + 1) / 2 ^ x by
        intro x
        by_cases hx : 0 ≤ x
        · have : (x.toNat : ℤ) = x := by simp [hx]
          specialize h x.toNat
          rw [this] at h
          rw [h, ← this]
          norm_cast
        · have xcast : ((-x).toNat : ℤ) = -x := by omega
          have : ((2 : ℝ) ^ (2 * x) + 1) / 2 ^ x = (2 ^ (2 * (-x)) + 1) / 2 ^ (-x) := by
            field_simp
            rw [add_mul, ← zpow_add₀ (by simp), mul_assoc]
            rw [← zpow_add₀ (by simp), add_mul, ← zpow_add₀ (by simp)]
            ring_nf
          rw [this]
          specialize h (-x).toNat
          rw [← xcast]
          rw [xcast, hfeven x] at h
          push_neg at hx
          rw [h]
          rfl
      -- We proceed by strong induction
      intro x
      induction' x using Nat.strong_induction_on with x ih
      match x with
      | 0 => norm_cast; rw [hf0]; norm_num
      | 1 => norm_cast
      | x + 2 =>
        push_cast
        rw [show (x : ℤ) + 2 = x + 1 + 1 by rfl]
        rw [hfrec, ← add_sub, sub_self, add_zero]
        norm_cast
        rw [ih (x + 1) (by simp), ih x (by simp)]
        push_cast
        ring
  · -- It remains to show that the provided function is a solution
    intro hf
    constructor
    · specialize hf 1
      norm_num at hf
      exact hf
    · intro x y
      rw [hf x, hf y, hf (x + y), hf (x - y)]
      rw [mul_add, mul_sub]
      have aux {x : ℤ} : (2 : ℝ) ^ (2 * x) = (2 ^ x) ^ 2 := by
        rw [two_mul, zpow_add₀ (by simp), pow_two]
      field_simp [zpow_sub₀, zpow_add₀, aux]
      ring
