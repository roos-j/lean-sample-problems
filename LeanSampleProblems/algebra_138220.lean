import Mathlib

open Finset

/- The function $f(x)$ is defined on $\mathbf{R}$, and for any real number $x$, it holds that $f(1+x)=f(3-x)$, and $f(2+x)=$ $-f(4-x)$.
Find the value of $f(1)+f(2)+\cdots+f(100)$. -/
theorem algebra_138220 (f : ℝ → ℝ) (h1 : ∀ x, f (1 + x) = f (3 - x)) (h2 : ∀ x, f (2 + x) = -f (4 - x)) :
    ∑ i ∈ range 100, f (i + 1) = 0 := by
  -- The assumptions imply the following:
  have h3 : ∀ x, f (x + 2) = - f x := by
    intro x; symm
    calc
      _ = - f (1 + (x - 1)) := by congr; simp
      _ = - f (3 - (x - 1)) := by congr! 1; exact h1 _
      _ = - f (4 - x) := by congr! 2; ring
      _ = _ := by rw [(h2 _).symm, add_comm]
  -- Applying this twice implies that `f` is `4`-periodic
  have h4: ∀ x, f (x + 4) = f x := by
    intro x
    calc
      _ = f ((x + 2) + 2) := by congr! 1; ring
      _ = - f (x + 2) := h3 _
      _ = f x := by rw [h3, neg_neg]
  -- Then by induction:
  have h5: ∀ k : ℕ, ∀ x, f (4 * k + x) = f x := by
    intro k
    induction' k with k ih
    · simp
    · intro x
      push_cast
      rw [mul_add, add_assoc, ih _, add_comm, mul_one, h4]
  -- We prove an auxiliary lemma for evaluating this sum:
  have sum_range_mul (n : ℕ) (t : ℕ) {a : ℕ → ℝ} : ∑ k ∈ range (n * t), a k =
      ∑ i ∈ range n, ∑ s ∈ range t, a (i * t + s) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ← ih]; rw [add_mul, one_mul, sum_range_add]
  -- This allows us to evaluate the sum in question:
  calc
    _ = ∑ i ∈ range 25, ∑ s ∈ range 4, f (4 * i + (s + 1)) := by
      convert sum_range_mul 25 4 using 3
      norm_cast
      ring_nf
    _ = 25 * (f 1 + f 2 + f 3 + f 4) := by
      simp_rw [h5]
      simp [sum_range_succ]
      ring_nf
    _ = _ := by
      rw [show (3 : ℝ) = 1 + 2 by norm_num, h3 1]
      rw [show (4 : ℝ) = 2 + 2 by norm_num, h3 2]
      ring
