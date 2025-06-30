import Mathlib

open Real

/- Let $m$ be the largest real solution to the equation
$$3/(x−3) + 5/(x−5) + 17/(x−17) + 19/(x−19) = x^2 − 11x − 4.$$
There are positive integers $a$, $b$, and $c$ such that $m=a + \sqrt{b + \sqrt{c}}$.
Find $a+b+c$. -/
theorem algebra_95863 (S : Set ℝ) (m : ℝ)
    (hS : S = { x : ℝ | x - 3 ≠ 0 ∧ x - 5 ≠ 0 ∧ x - 17 ≠ 0 ∧ x - 19 ≠ 0 ∧
      3 / (x - 3) + 5 / (x - 5) + 17 / (x - 17) + 19 / (x - 19) = x ^ 2 - 11 * x - 4 })
    (hm : IsGreatest S m) : ∃ a b c : ℕ, m = a + √(b + √c) ∧ a + b + c = 263 := by
  -- (Implementation note: moving existence of `a b c` into the conclusion is convenient for formalization and captures the intended problem)
  have aux1 : √800 = 2 * √200 := by
    calc  _ = √(2 ^ 2 * 200) := by norm_num
          _ = 2 * √200 := by simp
  have aux2 : 0 < 52 - √200 := by
    calc  _ < 52 - √(15 ^ 2) := by rw [sqrt_sq] <;> positivity
          _ < _ := by gcongr; norm_num
  -- Let's first show that the equation has the following solutions
  have x_eq {x : ℝ} (hxS: x ∈ S) : x = 0 ∨ x = 11 ∨ x = 11 + √(52 + √200) ∨ x = 11 - √(52 + √200) ∨
      x = 11 + √(52 - √200) ∨ x = 11 - √(52 - √200) := by
    by_cases hx0 : x = 0; focus { left; assumption }; push_neg at hx0
    by_cases hx11 : x = 11; focus { right; left; assumption }; push_neg at hx11
    rw [hS] at hxS
    obtain ⟨hx3, hx5, hx17, hx19, eq_x⟩ := hxS
    -- If we add 4 on both sides of the equation, we get:
    have eq1 : 1 / (x - 3) + 1 / (x - 5) + 1 / (x - 17) + 1 / (x - 19) = x - 11 := by
      symm; calc
        _ = ((x ^ 2 - 11 * x - 4) + 4) / x := by field_simp; ring
        _ = _ := by rw [← eq_x]; field_simp; ring
    -- Substituting `y = m - 11` we get the following equation
    set y := x - 11 with y_def
    have eq2 : 1 / (y + 8) + 1 / (y - 8) + 1/ (y + 6) + 1 / (y - 6) = y := by
      rw [y_def]; rw [y_def] at eq1; nth_rewrite 5 [← eq1]; ring
    have hy0 : y ≠ 0 := by
      by_contra h
      have : x = 11 := by linarith only [y_def, h]
      rw [this] at hx11
      exact False.elim <| hx11 rfl
    -- Grouping terms this implies
    have eq3 : 2 * y * (y ^ 2 - 6 ^ 2) + 2 * y * (y ^ 2 - 8 ^ 2) = y * (y ^ 2 - 6 ^ 2) * (y ^ 2 - 8 ^ 2) := by
      field_simp at eq1; rw [y_def] at eq1; ring_nf at eq1; rw [y_def]; ring_nf; exact eq1
    -- Since `y` is not `0` we can cancel out `y` on both sides
    -- Substituting `z = (x - 11) ^ 2` we get
    set z := y ^ 2 with z_def
    have eq4 : 2 * (z - 6 ^ 2) + 2 * (z - 8 ^ 2) = (z - 6 ^ 2) * (z - 8 ^ 2) := by
      refine mul_left_cancel₀ hy0 ?_; rw [← mul_assoc, ← eq3]; ring
    -- This implies that `z` satisfies a quadratic equation
    have eq5 : 1 * (z * z) + (- 104) * z + 2504 = 0 := by linarith only [eq4]
    have eq_or_eq_neg_of_sq_eq {y z : ℝ} (hz : 0 ≤ z) : y ^ 2 = z → y = √z ∨ y = -√z := by
      intro h
      rw [← sq_sqrt hz] at h
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h
    -- Using the quadratic equation and subsituting back we get the value of `x` and thereby of `a, b, c`
    have : discrim 1 (-104) 2504 = √800 * √800 := by rw [discrim]; norm_num
    have z_eqor := (quadratic_eq_zero_iff (by norm_num) this z).mp eq5
    rw [z_def] at z_eqor
    simp [add_div, sub_div] at z_eqor
    rw [aux1] at z_eqor
    norm_num at z_eqor
    obtain hysq | hysq := z_eqor
    · obtain hz | hz := eq_or_eq_neg_of_sq_eq (by positivity) hysq
      · right; right; left; linarith only [hz, y_def]
      · right; right; right; left; linarith only [hz, y_def]
    · obtain hz | hz := eq_or_eq_neg_of_sq_eq (by positivity) hysq
      · right; right; right; right; left; linarith only [hz, y_def]
      · right; right; right; right; right; linarith only [hz, y_def]
  set u := 11 + √(52 + √200) with u_def
  have hppS : u ∈ S := by -- Verify that `u` is a solution
    rw [hS]
    have : 0 < u - 19 := by
      calc _ = -8 + √(8 ^ 2) := by rw [sqrt_sq]; norm_num; positivity
           _ = -8 + √(52 + √(12 ^ 2)) := by congr; rw [sqrt_sq]; norm_num; positivity
           _ < -8 + √(52 + √200) := by gcongr; norm_num
           _ = _ := by rw [u_def]; ring
    have : u - 19 ≠ 0 := ne_of_gt this
    have : u - 3 ≠ 0 := by
      apply ne_of_gt; calc
        _ < u - 19 := by assumption
        _ < _ := by norm_num
    have : u - 5 ≠ 0 := by
      apply ne_of_gt; calc
        _ < u - 19 := by assumption
        _ < _ := by norm_num
    have : u - 17 ≠ 0 := by
      apply ne_of_gt; calc
        _ < u - 19 := by assumption
        _ < _ := by norm_num
    refine ⟨by assumption, by assumption, by assumption, by assumption, ?_⟩
    field_simp; ring_nf
    have pow_three (x : ℝ) : x ^ 3 = x ^ 2 * x := by ring
    have pow_four (x : ℝ) : x ^ 4 = x ^ 2 * x ^ 2 := by ring
    have pow_five (x : ℝ) : x ^ 5 = x ^ 2 * x ^ 2 * x := by ring
    have pow_six (x : ℝ) : x ^ 6 = x ^ 2 * x ^ 2 * x ^ 2:= by ring
    rw [pow_three, pow_four, pow_five, pow_six]
    simp only [sq_sqrt (show 0 ≤ 52 + √200 by positivity)]; ring_nf
    rw [pow_three]; simp only [Nat.ofNat_nonneg, sq_sqrt]; ring
  have aux_mp : 11 - √(52 + √200) < 11 + √(52 + √200) := by
    linear_combination Left.neg_lt_self (show 0 < √(52 + √200) by positivity)
  have aux_pm : 11 + √(52 - √200) < 11 + √(52 + √200) := by
    gcongr; linear_combination Left.neg_lt_self (show 0 < √200 by positivity)
  have aux_mm : 11 - √(52 - √200) < 11 + √(52 + √200) := by
    calc
      _ < 11 + √(52 - √200) := by
        linear_combination Left.neg_lt_self (show 0 < √(52 - √200) by positivity)
      _ < _ := aux_pm
  -- Since `m` is the largest solution we get the values of `m` and thus `a, b, c`
  have m_eq : m = 11 + √(52 + √200) := by
    obtain ⟨hmS, m_max⟩ := hm
    have le_m := m_max hppS
    -- rw [hS] at hm
    obtain h|h|h|h|h|h := x_eq hmS <;> rw [h] at le_m
    · suffices (0 : ℝ) < 0 by norm_num at this
      calc
        _ < 11 + √(52 + √200) := by positivity
        _ ≤ 0 := le_m
    · exact False.elim <| lt_irrefl _ <| Trans.trans le_m (show 11 < u by rw [u_def]; simp; positivity)
    · assumption
    · exact False.elim <| lt_irrefl _ <| Trans.trans le_m aux_mp
    · exact False.elim <| lt_irrefl _ <| Trans.trans le_m aux_pm
    · exact False.elim <| lt_irrefl _ <| Trans.trans le_m aux_mm
  have notsq : ¬∃ k, 200 = k ^ 2 := by
    push_neg; intro k
    by_cases hk: k < 15
    · interval_cases k <;> norm_num
    · push_neg at hk; apply ne_of_lt
      calc
        _ < 15 ^ 2 := by norm_num
        _ ≤ k ^ 2 := by gcongr
  use 11, 52, 200
  exact ⟨m_eq, rfl⟩


--- Alternate version:

-- theorem algebra_95863 (S : Set ℝ) (m : ℝ) (a b c : ℕ)
--     (hS : S = { x : ℝ | x - 3 ≠ 0 ∧ x - 5 ≠ 0 ∧ x - 17 ≠ 0 ∧ x - 19 ≠ 0 ∧
--       3 / (x - 3) + 5 / (x - 5) + 17 / (x - 17) + 19 / (x - 19) = x ^ 2 - 11 * x - 4 })
--     (haux : ∀ {a' b' c' : ℕ}, a + √(b + √c) = a' + √(b' + √c') ∧ (¬∃ k, c' = k ^2) → a = a' ∧ b = b' ∧ c = c')
--     (hm : IsGreatest S m) (hm' : m = a + √(b + √c)) : a + b + c = 263 := by
--   -- (Implementation note: `haux` is okay to assume here; this is considered not even worth justifying in informal solutions, but somewhat lengthy to formalize)


--- End of proof for this version:
-- rw [hm'] at m_eq
-- obtain ⟨a_eq, b_eq, c_eq⟩ := haux ⟨m_eq, notsq⟩
-- rw [a_eq, b_eq, c_eq]
