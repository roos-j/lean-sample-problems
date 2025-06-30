import Mathlib

open Finset Real

/- Let $a_{1}, a_{2}, \cdots, a_{n}$ be real numbers, and $S$ be a non-negative real number, such that
(1) $a_{1} \leqslant a_{2} \leqslant \cdots \leqslant a_{n}$;
(2) $a_{1}+a_{2}+\cdots+a_{n}=0$;
(3) $\left|a_{1}\right|+\left|a_{2}\right|+\cdots+\left|a_{n}\right|=S$.
Prove: $a_{n}-a_{1} \geqslant \frac{2 S}{n}$. -/
theorem inequalities_120835 {n : ℕ} {S : ℝ} (hn : 0 < n) (a : ℕ → ℝ)
    (hinc : ∀ i j, i ≤ j → a i ≤ a j) (hsum : ∑ i ∈ range n, a i = 0)
    (habs : ∑ i ∈ range n, |a i| = S) :
    a (n - 1) - a 0 ≥ 2 * S / n := by
  /- Implementation note: We use `range n` in place of `{1, 2, .., n}` as index set. This does not change the mathematical content of the problem.
  For convenience we omit `i j ∈ range n` in `hinc`. This has no impact on the math. -/
  -- Note that `0 ≤ S` by `habs`
  have S_nonneg : 0 ≤ S := by rw [← habs]; exact sum_nonneg <| fun _ _ ↦ abs_nonneg _

  -- If `S` is zero there is nothing to show, so we may assume `0 < S`
  by_cases hS : S = 0; focus {
      rw [hS] at habs
      have := (sum_eq_zero_iff_of_nonneg (by simp)).mp habs
      simp only [mem_range, abs_eq_zero] at this
      rw [this _ (by omega), this _ (by omega), sub_zero, hS, mul_zero, zero_div]
  }
  have S_pos : 0 < S := by positivity

  -- We have `a 0 < 0` since otherwise `S` would be zero
  have a0 : a 0 < 0 := by
    by_contra h
    simp at h
    have : ∀ i, 0 ≤ a i := fun _ ↦ Trans.trans h (hinc _ _ (by positivity))
    have : S = 0 := by
      calc
        _ = ∑ i ∈ range n, |a i| := habs.symm
        _ = ∑ i ∈ range n, a i := by congr!; exact abs_of_nonneg <| this _
        _ = 0 := hsum
    contradiction

  -- We have `0 ≤ a (n - 1)`  since otherwise `S` would be zero
  have ansub1 : 0 ≤ a (n - 1) := by
    by_contra h
    simp at h
    have : ∀ i ∈ range n, a i < 0 := fun _ hi ↦ Trans.trans (hinc _ _ (by simp at hi; omega)) h
    have : S = 0 := by
      calc
        _ = ∑ i ∈ range n, |a i| := habs.symm
        _ = -∑ i ∈ range n, a i := by rw [← sum_neg_distrib]; congr! 1 with i hi; exact abs_of_neg <| this i hi
        _ = 0 := by rw [hsum, neg_zero]
    contradiction

  -- By `hsum` not all `a i` can be positive, so by `hinc` there must be `k` such that `a k < 0 ≤ a (k + 1)`
  have : ∃ k ∈ range n, 0 < k ∧ a (k - 1) < 0 ∧ 0 ≤ a k := by
    obtain ⟨k, hk⟩ := min_of_mem (s := {i ∈ range n | 0 ≤ a i}) (a := n - 1) (by simp; exact ⟨hn, by assumption⟩)
    have : 0 < k := by
      by_contra h
      have := (mem_filter.mp <| mem_of_min hk).2
      rw [show k = 0 by omega] at this
      linarith only [a0, this]
    have := (mem_filter.mp <| mem_of_min hk).1
    have : k < n := mem_range.mp this
    have : a (k - 1) < 0 := by -- follows by minimality of `k`
      convert not_mem_of_lt_min (show k - 1 < k by omega) hk using 1
      simp; left; omega
    have : 0 ≤ a k := (mem_filter.mp <| mem_of_min hk).2
    use k

  obtain ⟨k, hk, hk0, hk1, hk2⟩ := this

  have : 0 < n - (k : ℝ) := by
    simp at hk
    calc
      _ = (n : ℝ) - n := by rw [sub_self]
      _ < n - k := by gcongr
  simp only [mem_range] at hk
  have : k ≤ n - 1 := by omega

  -- Then `habs` can be rewritten as:
  have e0 : - ∑ i ∈ range k, a i + ∑ i ∈ range (n - k), a (k + i) = S := by
    rw [← sum_neg_distrib, ← habs]
    conv => enter [2, 1, 1]; rw [show n = k + (n - k) by omega]
    rw [sum_range_add]
    congr! 2 with i hi i hi
    · refine (abs_of_neg ?_).symm
      calc
        _ ≤ a (k - 1) := by exact hinc _ _ (by have := mem_range.mp hi; omega)
        _ < 0 := by assumption
    · refine (abs_of_nonneg ?_).symm
      calc
        _ ≤ a k := by assumption
        _ ≤ a (k + i) := by exact hinc _ _ (by omega)

  -- Rewrite `hsum` similarly:
  have e0' : ∑ i ∈ range k, a i + ∑ i ∈ range (n - k), a (k + i) = 0 := by
    rw [← hsum]
    conv => enter [2, 1, 1]; rw [show n = k + (n - k) by omega]
    rw [sum_range_add]

  -- Combining this with `hsum` we get:
  have e1 : ∑ i ∈ range k, -a i = S / 2 := by rw [sum_neg_distrib]; linarith only [e0, e0']
  have e2 : ∑ i ∈ range (n - k), a (k + i) = S / 2 := by linarith only [e0, e0']

  -- Then `e1` implies a lower bound for `-a 0`
  have e3 : - a 0 ≥ S / (2 * k) := by
    calc
      _ = ( k * (- a 0)) / k := by field_simp; exact mul_comm _ _
      _ = (∑ i ∈ range k, - a 0) / k := by field_simp
      _ ≥ (∑ i ∈ range k, - a i) / k := by gcongr; exact hinc _ _ (by positivity)
      _ = _ := by rw [e1]; field_simp

  -- `e2` implies a lower bound for `a (n - 1)`
  have e4 : a (n - 1) ≥ S / (2 * (n - k)) := by
    calc
      _ = ((n - k) * a (n - 1)) / (n - k) := by field_simp
      _ = (∑ i ∈ range (n - k), a (n - 1)) / (n - k) := by field_simp [show k ≤ n by omega]
      _ ≥ (∑ i ∈ range (n - k), a (k + i)) / (n - k) := by
        gcongr with i hi
        refine hinc _ _ (by simp only [mem_range] at hi; omega)
      _ = S / (2 * (n - k)) := by rw [e2]; field_simp

  -- We need the following consequence of `AM-GM`
  have e5: (n - k) * k ≤ n ^ 2 / (4 : ℝ) := by
    linarith only [show 0 ≤ (((n: ℝ) - k) - k) ^ 2 by exact sq_nonneg _]

  -- Combined, `e3` and `e4` imply the claim
  calc
    _ = a (n - 1) + (- a 0) := by rfl
    _ ≥ S / (2 * (n - k)) + S / (2 * k) := by gcongr
    _ = S / 2 * n / ((n - k) * k) := by field_simp; ring
    _ ≥ S / 2 * n / (n ^ 2 / 4) := by gcongr
    _ = _ := by field_simp; ring
  