import Mathlib

/-
Prove that the following equations have no solutions in integers:
a) $x^{2}+y^{2}=2003$

b) $12 x+5=y^{2}$

c) $-x^{2}+7 y^{3}+6=0$

d) $x^{2}+y^{2}+z^{2}=1999$

e) $15 x^{2}-7 y^{2}=9$
f) $x^{2}-5 y+3=0$

g) $x_{1}^{4}+\ldots+x_{14}^{4}=1999$;

h) $8 x^{3}-13 y^{3}=17$. -/
theorem number_theory_206892 :
    (¬∃ x y : ℤ, x ^ 2 + y ^ 2 = 2003) ∧
    (¬∃ x y : ℤ, 12 * x + 5 = y ^ 2) ∧
    (¬∃ x y : ℤ, -x ^ 2 + 7 * y ^ 3 + 6 = 0) ∧
    (¬∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 1999) ∧
    (¬∃ x y : ℤ, 15 * x ^ 2 - 7 * y ^ 2 = 9) ∧
    (¬∃ x y : ℤ, x ^ 2 - 5 * y + 3 = 0) ∧
    (¬∃ x : Fin 14 → ℤ, ∑ i : Fin 14, (x i) ^ 4 = 1999) ∧
    (¬∃ x y : ℤ, 8 * x ^ 3 - 13 * y ^ 3 = 17) := by
  -- We first prove a lemma that seems to be missing from Mathlib
  have Int.pow_emod (a: ℤ) (b : ℕ) (n : ℤ) : a ^ b % n = (a % n) ^ b % n := by
    induction b with
    | zero => rfl
    | succ b ih => simp [Int.pow_succ, Int.mul_emod, ih]

  and_intros
  · -- There is no solution modulo 4
    by_contra h
    obtain ⟨x, y, hxy⟩ := h
    have : (x ^ 2 + y ^ 2) % 4 = 2003 % 4 := by rw [hxy]
    rw [Int.add_emod] at this
    have sq_mod_4 (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
      have : x % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
      have : 0 ≤ x % 4 := Int.emod_nonneg _ (by norm_num)
      rw [Int.pow_emod]
      interval_cases x % 4 <;> norm_num
    obtain hx | hx := sq_mod_4 x <;> obtain hy | hy := sq_mod_4 y
    all_goals { rw [hx, hy] at this; norm_num at this }
  · -- There is no solution modulo 3
    by_contra h
    obtain ⟨x, y, hxy⟩ := h
    have e : (12 * x + 5) % 3 = y ^ 2 % 3 := by rw [hxy]
    rw [Int.add_emod, Int.mul_emod, Int.pow_emod] at e
    norm_num at e
    have : y % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have : 0 ≤ y % 3 := Int.emod_nonneg _ (by norm_num)
    interval_cases y % 3 <;> norm_num at e
  · -- There is no solution modulo 7
    by_contra h
    obtain ⟨x, y, hxy⟩ := h
    have e : (-x ^ 2 + 7 * y ^ 3 + 6) % 7 = 0 := by rw [hxy]; norm_num
    rw [Int.add_emod, Int.add_emod (-x ^ 2), Int.mul_emod, Int.neg_emod, Int.sub_emod, Int.pow_emod x] at e
    have : x % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
    have : 0 ≤ x % 7 := Int.emod_nonneg _ (by norm_num)
    interval_cases x % 7 <;> norm_num at e
  · -- There is no solution modulo 8
    by_contra h
    obtain ⟨x, y, z, hxyz⟩ := h
    have e : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 1999 % 8 := by rw [hxyz]
    rw [Int.add_emod, Int.add_emod (x ^ 2)] at e
    have sq_mod_8 (x : ℤ) : (x ^ 2) % 8 = 0 ∨ (x ^ 2) % 8 = 1 ∨ (x ^ 2) % 8 = 4 := by
      have : x % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
      have : 0 ≤ x % 8 := Int.emod_nonneg _ (by norm_num)
      rw [Int.pow_emod x]
      interval_cases x % 8 <;> norm_num
    obtain hx | hx | hx := sq_mod_8 x <;> obtain hy | hy | hy := sq_mod_8 y <;> obtain hz | hz | hz := sq_mod_8 z
    all_goals { rw [hx, hy, hz] at e; norm_num at e }
  · -- There is no solution modulo 5
    by_contra h
    obtain ⟨x, y, hxy⟩ := h
    have e : (15 * x ^ 2 - 7 * y ^ 2) % 5 = 9 % 5 := by rw [hxy]
    rw [Int.sub_emod, Int.mul_emod, Int.mul_emod 7] at e
    have sq_mod_5 (x : ℤ) : (x ^ 2) % 5 = 0 ∨ (x ^ 2) % 5 = 1 ∨ (x ^ 2) % 5 = 4 := by
      have : x % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
      have : 0 ≤ x % 5 := Int.emod_nonneg _ (by norm_num)
      rw [Int.pow_emod x]
      interval_cases x % 5 <;> norm_num
    obtain hx | hx | hx := sq_mod_5 x <;> obtain hy | hy | hy := sq_mod_5 y
    all_goals { rw [hx, hy] at e; norm_num at e }
  · -- There is no solution modulo 5
    by_contra h
    obtain ⟨x, y, hxy⟩ := h
    have e : (x ^ 2 - 5 * y + 3) % 5 = 0 := by rw [hxy]; norm_num
    rw [Int.add_emod, Int.sub_emod, Int.mul_emod, Int.pow_emod] at e
    have : x % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
    have : 0 ≤ x % 5 := Int.emod_nonneg _ (by norm_num)
    interval_cases x % 5 <;> norm_num at e
  · -- There is no solution modulo 16 because each summand is at most `1` mod 16, but the right hand side is 15 mod 16
    by_contra h
    obtain ⟨x, hx⟩ := h
    have e : (∑ i : Fin 14, (x i) ^ 4) % 16 = 15 := by rw [hx]; norm_num
    rw [Finset.sum_int_mod] at e
    have pow_4_mod_16 (y : ℤ) : y ^ 4 % 16 ≤ 1 := by
      have : y % 16 < 16 := Int.emod_lt_of_pos _ (by norm_num)
      have : 0 ≤ y % 16 := Int.emod_nonneg _ (by norm_num)
      rw [Int.pow_emod]
      interval_cases y % 16 <;> norm_num
    have le_14 : ∑ i : Fin 14, (x i) ^ 4 % 16 ≤ 14 := by
      calc
        _ ≤ ∑ i : Fin 14, (1 : ℤ) := by gcongr; exact pow_4_mod_16 _
        _ = _ := by simp
    have : (∑ i : Fin 14, (x i) ^ 4 % 16) % 16 = ∑ i : Fin 14, (x i) ^ 4 % 16 := by
      refine Int.emod_eq_of_lt ?_ ?_
      · apply Finset.sum_nonneg
        exact fun _ _ ↦ Int.emod_nonneg _ (by norm_num)
      · exact Trans.trans le_14 (show 14 < 16 by norm_num)
    rw [this] at e
    suffices (15 : ℤ) ≤ 14 by norm_num at this
    calc
      _ = ∑ i : Fin 14, (x i) ^ 4 % 16 := by rw [← e]
      _ ≤ 14 := le_14
  · -- There is no solution modulo 13
    by_contra h
    obtain ⟨x, y, hxy⟩ := h
    have e : (8 * x ^ 3 - 13 * y ^ 3) % 13 = 17 % 13 := by rw [hxy]
    rw [Int.sub_emod, Int.mul_emod, Int.mul_emod 13, Int.pow_emod x] at e
    have : x % 13 < 13 := Int.emod_lt_of_pos _ (by norm_num)
    have : 0 ≤ x % 13 := Int.emod_nonneg _ (by norm_num)
    interval_cases x % 13 <;> norm_num at e
