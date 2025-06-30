import Mathlib

open Set Real

/- A function $f$ has domain [0,2] and range [0,1].
  (The notation [a,b] denotes $\{x : a \le x \le b\}$.)
  What are the domain and range, respectively, of the function $g$ defined by
  $g(x)=1−f(x+1)$ ?

  (A) [−1,1],[−1,0]
  (B) [−1,1],[0,1]
  (C) [0,2],[−1,0]
  (D) [1,3],[−1,0]
  (E) [1,3],[0,1]
   -/
theorem algebra_98507 {f g : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 2, f x ∈ Icc 0 1)
    (hg : g = fun x => 1 - f (x + 1)) : ∀ x ∈ Icc (-1) 1, g x ∈ Icc 0 1 := by
  -- It suffices to show that for all `x ∈ [-1, 1]` we have `g x ∈ [0, 1]`
  -- So let `x ∈ [-1, 1]`
  intro x hx
  -- Substituting the definition of `g` it suffices to show that
  suffices h :  f (x + 1) ≤ 1 ∧ 0 ≤ f (x + 1) by
    rw [hg]; simp; assumption
  -- This follows because `x + 1 ∈ [0,2]` so `f (x + 1) ∈ [0, 1]`
  have : x + 1 ∈ Icc 0 2 := ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  exact ⟨(hf (x+1) this).2, (hf (x+1) this).1⟩
