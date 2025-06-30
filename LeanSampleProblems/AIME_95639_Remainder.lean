import Mathlib

open Finset

/- For positive integers $n$ and $k$, let $f(n, k)$ be the remainder when $n$ is divided by $k$, and for $n > 1$ let $F(n) = \max_{\substack{1\le k\le \frac{n}{2}}} f(n, k)$. Find the remainder when $\sum\limits_{n=20}^{100} F(n)$ is divided by $1000$. -/
theorem number_theory_95639 {F : ℕ → ℕ} {f : ℕ → ℕ → ℕ}
    (hf : f = fun n k ↦ n % k) (hF : F = fun n ↦ sup (Icc 1 (n / 2)) (f n)) :
    (∑ n ∈ Icc 20 100, F n) % 1000 = 512 := by
  /- This can be solved directly by `decide`, but we follow a more likely human reasoning path -/
  -- The claim will follow if we can show that the supremum in the definition of `F n` is achieved when `k = [n/3] + 1`
  have F_eq (n : ℕ) (hn : 20 ≤ n) : F n = n / 3 + n % 3 - 2 := by
    by_cases hn : 21 ≤ n; swap; focus { interval_cases n; rw [hF, hf]; rfl } -- one case below requires `n ≥ 21`, so we treat `n = 20` manually
    let m := n / 3
    let r := n % 3
    have n_eq : n = 3 * m + r := Eq.symm (Nat.div_add_mod n _)
    have m_eq : m = n / 3 := by rfl
    have r_eq : r = n % 3 := by rfl
    have r_lt : r < 3 := Nat.mod_lt _ (by positivity)
    have mod_eq_sub_two_mul {n k : ℕ} (h : 2 * k ≤ n) (h' : n  - 2 * k < k) : n % k = n - 2 * k := by
      calc
        _ = (n - 2 * k) % k := by rw [Nat.mod_eq_sub_mod, Nat.mod_eq_sub_mod, ← Nat.sub_add_eq, Nat.two_mul]; apply Nat.le_sub_of_add_le; all_goals linarith only [h]
        _ = _ := Nat.mod_eq_of_lt h'
    have mul_add_mod {m r : ℕ} (h : r < m) : (3 * m + r) % m = r := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega)]
      rw [Nat.mod_eq_of_lt] <;> omega
    have n_mod_eq : n % (m + 1) = m + r - 2 := by
      rw [n_eq]
      calc
        _ = (3 * m + r) - 2 * (m + 1) := by exact mod_eq_sub_two_mul (by omega) (by omega)
        _ = _ := by omega
    rw [hF, ← m_eq, ← r_eq]
    dsimp
    apply le_antisymm
    · apply Finset.sup_le_iff.mpr
      rintro k hk
      obtain ⟨k_ge, k_le⟩ := mem_Icc.mp hk
      -- The claim follows by considering cases based on the size of `k`
      have : m + 1 ≤ k ∨ k = m ∨ k = m - 1 ∨ k ≤ m - 2 := by omega
      obtain h|h|h|h := this
      · calc
          _ = n - 2 * k := by rw [hf]; exact mod_eq_sub_two_mul (by omega) (by omega)
          _ ≤ _ := by omega
      · calc
          _ = r := by rw [hf, h, n_eq]; simp [mul_add_mod (show r < m by omega)]
          _ ≤ _ := by omega
      · calc
          _ = r + 3 := by
            rw [hf, h, n_eq]; dsimp;
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega)]
            rw [Nat.mod_eq_of_lt] <;> omega
          _ ≤ _ := by omega
      · calc
          _ = n % k := by rw [hf]
          _ ≤ k := by apply le_of_lt; exact Nat.mod_lt _ (by positivity)
          _ ≤ _ := by omega
    · calc
        _ = f n (m + 1) := by rw [← n_mod_eq, hf]
        _ ≤ _ := by apply Finset.le_sup; simp; omega
  have (n : ℕ) : F n = if 20 ≤ n then n / 3 + n % 3 - 2 else sup (Icc 1 (n / 2)) (fun k ↦ n % k) := by
    by_cases h : 20 ≤ n
    · simp [h, F_eq]
    · simp [h, hF, hf]
  simp_rw [this]; decide -- At this point `decide` is appropriate because this can be done quickly by a human
