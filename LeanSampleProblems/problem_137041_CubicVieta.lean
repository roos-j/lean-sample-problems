import Mathlib

open Polynomial Real

/- Find all real or complex roots of the system of equations

$$
\left\{\begin{array}{l}
x+y+z=3, \\
x^{2}+y^{2}+z^{2}=3, \\
x^{5}+y^{5}+z^{5}=3 .
\end{array}\right.
$$
 -/
theorem algebra_137041 {x y z : ℝ} (h1 : x + y + z = 3) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 3)
    (h3 : x ^ 5 + y ^ 5 + z ^ 5 = 3) : x = 1 ∧ y = 1 ∧ z = 1 := by
  -- Let `p` be the monic cubic polynomial with roots `x, y, z`
  let p : ℝ → ℝ := fun t ↦ (t - x) * (t - y) * (t - z)
  -- Factoring out we obtain Vieta's formulas
  let c := x * y * z
  let b := x * y + y * z + z * x
  let a := x + y + z
  have p_eq (t : ℝ) : p t = t ^ 3 - a * t ^ 2 + b * t - c := by simp only [p, a, b, c]; ring
  -- By assumption, `a = 3`
  have a_eq : a = 3 := h1
  -- Similarly we get `b = 3` from `h1, h2`
  have b_eq : b = 3 := by
    calc
      _ = ((x + y + z) ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2)) / 2 := by ring
      _ = _ := by rw [h1, h2]; norm_num
  -- Next we observe that
  have aux (n : ℕ) {t : ℝ} (ht : p t = 0) : t ^ (n + 3) - a * t ^ (n + 2) + b * t ^ (n + 1) - c * t ^ n = 0 := by
    calc
      _ = t ^ n * p t := by rw [p_eq]; ring
      _ = 0 := by simp [ht]
  -- Let us apply this to the roots of `p`:
  have ex (n : ℕ) := aux n (show p x = 0 by simp [p])
  have ey (n : ℕ) := aux n (show p y = 0 by simp [p])
  have ez (n : ℕ) := aux n (show p z = 0 by simp [p])
  -- Let us define the sums of powers
  let S (n : ℕ) := x ^ n + y ^ n + z ^ n
  -- Then from adding `ex, ey, ez` we get
  have eS (n : ℕ) : (S (n + 3)) - a * (S (n + 2)) + b * (S (n + 1)) - c * S n = 0 := by linear_combination (ex n) + (ey n) + (ez n)
  -- This allows us to compute `S 3`, `S 4`, `S 5`:
  have S0 : S 0 = 3 := by simp [S]; norm_num
  have S1 : S 1 = 3 := by simp [S]; exact h1
  have S2 : S 2 = 3 := by simp only [S]; exact h2
  have S3 : S 3 = 3 * c := by -- using `eS` with `n = 0`
    have := eS 0
    simp [S2, S1, S0, a_eq, b_eq] at this
    linarith only [this]
  have S4 : S 4 = 12 * c - 9 := by -- using `eS` with `n = 1`
    have := eS 1
    simp [S3, S2, S1, a_eq, b_eq] at this
    linarith only [this]
  have S5 : S 5 = 30 * c - 27 := by -- using `eS` with `n = 2`
    have := eS 2
    simp [S4, S3, S2, a_eq, b_eq] at this
    linarith only [this]
  -- Combining `S5` with assumption `h5` gives the value of `c`
  have c_eq : c = 1 := by linarith only [Trans.trans h3.symm S5]
  -- Then we conclude that `p` takes the following form
  have p_eq' (t : ℝ) : p t = (t - 1) ^ 3 := by rw [p_eq, a_eq, b_eq, c_eq]; ring
  -- Finally we need to show that `(t - 1) ^ 3 = (t - a) * (t - b) * (t - c)` for all `t` implies that `a = b = c = 1`.
  -- We do this using Mathlib's `Polynomial`
  let P : Polynomial ℝ := (X - C 1) ^ 3
  have P_eq : P = (X - C x) * (X - C y) * (X - C z) := by
    apply eq_of_infinite_eval_eq
    apply Set.infinite_of_forall_exists_lt <| fun a ↦ ⟨a - 1, ?_, by norm_num⟩
    simp [P]
    exact Trans.trans (p_eq' _).symm (show p _ = (_ - x) * (_ - y) * (_ - z) by simp only [p])
  have monic : P.Monic := by simp [P]; monicity!
  have ne_zero : P ≠ 0 := Monic.ne_zero monic
  have roots_eq : P.roots = {1, 1, 1} := by simp only [P, roots_pow, roots_X_sub_C]; rfl
  and_intros
  · have : x ∈ P.roots := by apply (mem_roots ne_zero).mpr; rw [P_eq]; simp
    rw [roots_eq] at this; simp at this; exact this
  · have : y ∈ P.roots := by apply (mem_roots ne_zero).mpr; rw [P_eq]; simp
    rw [roots_eq] at this; simp at this; exact this
  · have : z ∈ P.roots := by apply (mem_roots ne_zero).mpr; rw [P_eq]; simp
    rw [roots_eq] at this; simp at this; exact this
