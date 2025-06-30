import Mathlib

/- With three integers, the following was done: one number was decreased by one, one was increased by one, and the third number was squared. As a result, the same set of numbers was obtained. Find these numbers, given that the sum of the numbers is 2013. -/
theorem algebra_155560 {x y z : ℤ} (h : ({z, y, x} : Multiset ℤ) = {z ^ 2, y + 1, x - 1}) (h' : x + y + z = 2013) :
    x = 1007 ∧ y = 1006 ∧ z = 0 := by
  -- By assumption we obtain that the sums of the three numbers are equal:
  have h1 : x + y + z = (x - 1) + (y + 1) + z ^ 2 := by
    calc
      _ = ({z, y, x} : Multiset ℤ).sum := by simp; ring
      _ = ({z ^ 2, y + 1, x - 1} : Multiset ℤ).sum := by congr
      _ = _ := by simp; ring
  -- This implies that `z = z ^ 2`
  have h2 : z = z ^2 := by linarith only [h1]
  -- Then we must have `x = y + 1`
  have h3 : x = y + 1 := by
    rw [← h2] at h
    simp at h
    rw [Multiset.cons_eq_cons] at h
    obtain ⟨hx, h⟩ | ⟨hx, ⟨cs, hcs, hcs'⟩⟩ := h
    · linarith only [hx]
    · simp at hcs
      exact hcs.1
  -- Also, `z = z ^ 2` implies `z = 0` or `z = 1`
  have hz : z = 0 ∨ z = 1 := by
    by_cases h : z = 0
    · left; assumption
    · right
      push_neg at h
      rw [pow_two] at h2
      nth_rewrite 1 [← one_mul z] at h2
      exact (mul_right_cancel₀ h h2).symm
  -- Plugging this into `h'` we see that
  obtain hz|hz := hz
  · -- If `z = 0` we get values for `x, y`
    rw [hz] at h'
    rw [h3] at h'
    have : y = 1006 := by linarith only [h']
    have : x = 1007 := by linarith only [this, h3]
    and_intros <;> assumption
  · -- For `z = 1` there is no solution, because we get a contradiction to `h'`
    omega -- Obvious to humans, so it's okay to use `omega`
