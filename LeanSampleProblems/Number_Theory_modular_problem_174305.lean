import Mathlib

open EuclideanDomain

/-
For a 22-digit number $z$, the following properties are required:
$z$ has the unit digit 7; if this last digit is removed and placed in front of the remaining 21 digits, the result is the same as the multiplication $7 \cdot z$.
Prove that there is exactly one such number $z$! Determine this number! -/
theorem number_theory_174305 (z : ℤ) (hz : z % 10 = 7) (h : 7 * 10 ^ 21 + z / 10 = 7 * z) :
    z = 1014492753623188405797 := by
  -- Note: This can be solved by `omega`, but we provide human reasoning steps.
  -- Removing the last digit we get
  let x := z / 10
  -- Then `z` can be written as:
  have h0 : z = 10 * x + 7 := by
    convert (div_add_mod z 10).symm
    exact hz.symm
  -- From the assumption:
  have h1 : 7 * 10 ^ 21 + x = 7 * (10 * x + 7) := by linarith only [h, h0]
  -- Rearranging we get:
  have h2: 69 * x = 7 * 10 ^ 21 - 49 := by linarith only [h1]
  -- Dividing by `69` gives the claim
  have h3 : x = (7 * 10 ^ 21 - 49) / 69 := by
    calc
      _ = 69 * x / 69 := by rw [Int.mul_ediv_cancel_left x (by norm_num)]
      _ = _ := by rw [h2]
  rw [h0, h3]
  rfl
