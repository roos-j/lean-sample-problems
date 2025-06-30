import Mathlib

open Complex Finset

/- For what value of $n$ is $i + 2i^2 + 3i^3 + \cdots + ni^n = 48 + 49i$?
Note: here $i = \sqrt{-1}$.
$\textbf{(A)}\ 24 \qquad \textbf{(B)}\ 48 \qquad \textbf{(C)}\ 49 \qquad \textbf{(D)}\ 97 \qquad \textbf{(E)}\ 98$ -/
theorem algebra_93400 (n : ℕ) :
    (∑ k ∈ range n, (k + 1) * (I ^ (k + 1))) = 48 + I * 49 ↔ n = 97 := by
  -- Since `i^4=1` it is natural to sum four subsequent terms at a time which always gives `2 + 2 * I`
  have I_cube : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_mul, one_mul]
  have eq1 (m : ℕ) : ∑ r ∈ range 4, (4 * m + r + 1) * I ^ (4 * m + r + 1) = 2 - 2 * I := by
    simp_rw [pow_add, pow_mul, I_pow_four, one_pow, one_mul]; repeat rw [sum_range_succ]
    simp [I_cube]; ring
  let m := n / 4 -- Integer division!
  let r := n % 4
  have n_eq : n = 4 * m + r := Eq.symm (Nat.div_add_mod n 4)
  have sum_range_mul (n : ℕ) (t : ℕ) (a : ℕ → ℂ) : ∑ k ∈ range (t * n), a k = ∑ i ∈ range n, ∑ s ∈ range t, a (t * i + s) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ← ih]; rw [mul_add, mul_one, sum_range_add]
  -- Grouping terms by four we can compute the sum in question
  have eq2 : ∑ k ∈ range n, (k + 1) * (I ^ (k + 1)) = m * 2 - m * 2 * I + (∑ s ∈ range r, (4 * m + s + 1) * I ^ (s + 1)) := by
    calc
      _ = (∑ j ∈ range (4 * m), _) + (∑ s ∈ range r, _) := by rw [n_eq]; rw [sum_range_add]
      _ = (∑ j ∈ range m, ∑ s ∈ range 4, (4 * j + s + 1) * I ^ (4 * j + s + 1)) +
            (∑ s ∈ range r, (4 * m + s + 1) * I ^ (s + 1))  := by
        rw [sum_range_mul]; norm_cast; congr; ext; rw [add_assoc, pow_add, pow_mul, I_pow_four]; ring
      _ = _ := by simp_rw [eq1]; simp; ring
  have r_def : n % 4 = r := by rfl
  have r_lt : r < 4 := Nat.mod_lt _ (by positivity)
  rw [eq2]
  -- Then we can check the four different remainders and see that the only possible value of `n` is `97`
  interval_cases r
  all_goals rw [Complex.ext_iff]; simp [sum_range_succ, I_cube]; ring_nf
  · constructor
    · rintro ⟨h1, h2⟩; exact False.elim <| by linarith only [h1, h2]
    · intro h; simp [m]; rw [h] at r_def; norm_num at r_def
  · constructor
    · rintro ⟨h1, _⟩; norm_cast at h1; linarith only [n_eq, h1]
    · intro hn; simp [m, hn]; norm_num
  · constructor
    · rintro ⟨h1, h2⟩; exact False.elim <| by linarith only [h1, h2]
    · intro h; simp [m]; rw [h] at r_def; norm_num at r_def
  · constructor
    · rintro ⟨h1, h2⟩; exact False.elim <| by linarith only [h1, h2]
    · intro h; simp [m]; rw [h] at r_def; norm_num at r_def
