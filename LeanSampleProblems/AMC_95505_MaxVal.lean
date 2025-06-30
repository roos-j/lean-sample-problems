import Mathlib

/- In the expression $c*a^b−d$, the values of $a, b, c$, and $d$ are 0, 1, 2, and 3, although not necessarily in that order.
What is the maximum possible value of the result?

(A) 5
(B) 6
(C) 8
(D) 9
(E) 10
-/
theorem algebra_95505 (a b c d : ℕ) (hc : c < 4) (h : ({a, b, c, d} : Set ℕ) = {0, 1, 2, 3}) :
    1 * 3 ^ 2 - 0 = 9 ∧ c * a ^ b - (d : ℤ) ≤ 9 := by
  -- First notice that the value `9` is achieved when `(a, b, c) = (3, 2, 1)`
  constructor
  focus { norm_num }
  -- Rewrite the inequality as `c * a^b ≤ d + 9`
  simp; norm_cast
  -- If `b = 0` we get the claim because `c < 4`
  by_cases hb': b = 0
  focus {
      rw [hb']; simp; linarith only [hc]
  }
  -- Thus let `b ≠ 0`; if we assume `a = 0` or `c = 0` we also get the claim because `d ≥ 0`
  by_cases ha' : a = 0
  focus { rw [ha', zero_pow hb']; linarith only }
  by_cases hc' : c = 0
  focus { rw [hc', zero_mul]; linarith only }
  -- Since one of the values must be zero, it must be `d = 0`
  simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hd' : d = 0 := by
    specialize h 0
    tauto
  rw [hd'] at h
  rw [hd', add_zero]
  -- Now we have one of six cases and we can check that in each case the condition is true
  have h1 := h 1; simp at h1
  have h2 := h 2; simp at h2
  have h3 := h 3; simp at h3
  obtain ⟨e1|e1|e1,e2|e2|e2,e3|e3|e3⟩ := And.intro h1 (And.intro h2 h3)
    <;> try { rw [← e2] at e1; contradiction }
    <;> try { rw [← e3] at e1; contradiction }
    <;> try { rw [← e3] at e2; contradiction }
    <;> { rw [← e1, ← e2, ← e3]; norm_num }
