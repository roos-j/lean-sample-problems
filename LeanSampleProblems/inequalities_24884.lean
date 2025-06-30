import Mathlib

namespace inequalities_24884

open Real Finset

/- Auxiliary estimate using AM-GM -/
lemma l_amgm_aux {n : ℕ} {i : Fin (n + 1)} {a : Fin (n + 1) → ℝ} (ha : ∀ i, 0 < a i) (hn : 0 < n) : (∏ j ∈ univ.erase i, a j) ^ ((1 : ℝ) / n) ≤ (1 / n) * ∑ j ∈ univ.erase i, a j := by
  have haux : ∀ j ∈ univ.erase i, 0 ≤ a j := fun _ _ ↦ le_of_lt <| ha _
  have := geom_mean_le_arith_mean_weighted (univ.erase i) (fun _ ↦ 1 / n) a ?_ ?_ ?_
  · rw [← finset_prod_rpow _ _ haux]
    rw [← mul_sum] at this
    exact this
  · exact fun _ _ ↦ by positivity
  · field_simp
  · exact haux

/- An auxiliary combinatorial identity, trivial to humans -/
lemma l_aux1 {n : ℕ} {a : Fin (n + 1) → ℝ} (ha : ∀ i, 0 < a i) (hn : 0 < n) : ∏ i, a i = ∏ i, (∏ j ∈ univ.erase i, a j) ^ ((1 : ℝ) / n) := by
  have haux : 0 ≤ ∏ i, a i := le_of_lt <| prod_pos <| fun i _ ↦ ha i
  rw [← pow_rpow_inv_natCast (n := n) haux (by omega), one_div]
  rw [finset_prod_rpow (hs := fun _ _ ↦ le_of_lt <| prod_pos <| fun i _ ↦ ha i)]
  congr! 1
  simp_rw [← filter_ne, prod_filter]
  rw [prod_comm]
  simp_rw [← prod_filter, ne_comm, filter_ne, prod_const]
  rw [← Finset.prod_pow]
  congr! 2
  simp

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ be positive real numbers such that $a_{1}+a_{2}+$ $\cdots+a_{n}<1$. Prove that
$$
 \frac{a_{1} a_{2} \cdots a_{n}\left[1-\left(a_{1}+a_{2}+\cdots+a_{n}\right)\right]}{\left(a_{1}+a_{2}+\cdots+a_{n}\right)\left(1-a_{1}\right)\left(1-a_{2}\right) \cdots\left(1-a_{n}\right)} \leq \frac{1}{n^{n+1}} .
$$
 -/
theorem inequalities_24884 {n : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i < 1) :
    (∏ i, a i) * (1 - ∑ j, a j) / ((∑ j, a j) * ∏ i, (1 - a i)) ≤ 1 / (n ^ (n + 1)) := by
  -- Observe that `a i < 1`
  have ha' : ∀ i, a i < 1 := by
    intro i
    calc
      _ = ∑ j : Fin n, if j = i then a i else 0 := by simp
      _ ≤ ∑ j : Fin n, a j := by
        gcongr with j
        split_ifs with hi
        · rw [hi]
        · exact le_of_lt <| ha _
      _ < _ := hsum
  have nonempty := univ_nonempty_iff.mpr <| Fin.pos_iff_nonempty.mp hn
  -- By setting `a (n + 1) = ∑ i, a i` it suffices to show the following:
  suffices h : ∀ a : Fin (n + 1) → ℝ, (∀ i, 0 < a i) → (∀ i, a i < 1) → (∑ i, a i = 1) → (∏ i, a i) / (∏ i, (1 - a i)) ≤ 1 / (n ^ (n + 1)) by {
    let A : Fin (n + 1) → ℝ := fun i ↦ if hi : i = 0 then 1 - (∑ i, a i) else a (i.pred hi)
    have hA : ∀ i, 0 < A i := by
      intro i
      by_cases hi : i = 0
      · simp only [hi, A, sub_pos, reduceDIte]
        exact hsum
      · push_neg at hi; simp [A, hi]; exact ha _
    have haux {i : Fin n} : A i.succ = a i := by simp [A, Fin.succ_ne_zero]
    have hsum : ∑ i, A i = 1 := by
      rw [Fin.sum_univ_succ]
      simp_rw [haux]
      simp [A]
    have hA' : ∀ i, A i < 1 := by
      -- This hypothesis could be omitted, but we'd then have to derive it from `hA`, `hsum` below anyways
      intro i
      by_cases hi : i = 0
      · simp only [hi, reduceDIte, sub_lt_self_iff, A]
        apply sum_pos _ nonempty
        simp only [mem_univ, forall_const]
        exact ha
      · simp only [hi, reduceDIte, A]
        exact ha' _
    specialize h A hA hA' hsum
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at h
    rw [show A 0 = 1 - ∑ i, a i by rfl] at h
    rw [sub_sub_cancel, mul_comm] at h
    simp_rw [haux] at h
    exact h
  }
  clear * - nonempty hn
  intro a ha ha' hsum
  have hpos : 0 < ∏ i, (1 - a i) := by
    apply prod_pos
    intro i _
    linarith only [ha' i]
  -- Multiplying the inequalities `l_amgm_aux` for all `i` we get the inequality we need
  apply div_le_of_le_mul₀ (le_of_lt hpos) (by positivity)
  rw [l_aux1 ha hn]
  calc
    _ ≤ ∏ i, (1 / n) * ∑ j ∈ univ.erase i, a j := by
      gcongr
      · intro i _
        apply le_of_lt
        apply rpow_pos_of_pos
        apply prod_pos
        exact fun i _ ↦ ha i
      · exact l_amgm_aux ha hn
    _ = ∏ i, (1 / n) * (1 - a i) := by
      congr! 2 with i
      rw [← sum_erase_add _ _ (mem_univ i)] at hsum
      linarith only [hsum]
    _ = _ := by
      rw [prod_mul_distrib]
      simp

end inequalities_24884
