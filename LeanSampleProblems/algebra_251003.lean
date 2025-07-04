import Mathlib

open Real Finset

/- 7. (CAN 5)

  Let $a$ be a positive integer and let $\left\{a_{n}\right\}$ be defined by $a_{0}=0$ and

$$a_{n+1}=\left(a_{n}+1\right) a+(a+1) a_{n}+2 \sqrt{a(a+1) a_{n}\left(a_{n}+1\right)} \quad(n=1,2 \ldots) .$$

Show that for each positive integer $n, a_{n}$ is a positive integer.
-/
theorem algebra_251003 (a : ℕ) (ha : 0 < a)
    (as : ℕ → ℝ)
    (h_a0 : as 0 = 0)
    (h_an : ∀ n, as (n + 1) = (as n + 1) * a + (a + 1) * as n +
      2 * √(a * (a + 1) * as n * (as n + 1))) :
    ∀ n, 0 < n → ∃ m : ℕ, 0 < m ∧ as n = m := by
  -- Note the value of `as 1`
  have as_one : as 1 = a := by
    simp [h_an, h_a0]
  -- First observe that sequence elements are positive (up to the `0`th)
  have as_pos {n : ℕ} (hn : 1 ≤ n) : 0 < as n := by
    induction' n, hn using Nat.le_induction with n ih
    · rw [as_one]
      exact_mod_cast ha
    · rw [h_an]
      positivity
  have as_nonneg {n : ℕ} : 0 ≤ as n := by
    induction' n with n ih
    · rw [h_a0]
    · exact le_of_lt <| as_pos (by omega)
  -- Note the following identities from the definition:
  have h1 (n : ℕ) : √(as (n + 1)) = √(as n) * √(a + 1) + √(as n + 1) * √a := by
    calc
      _ = √((√(as n) * √(a + 1) + √(as n + 1) * √a) ^ 2) := by
        have := as_nonneg (n := n)
        rw [h_an]
        congr
        rw [add_sq, mul_pow, mul_pow, sq_sqrt as_nonneg, sq_sqrt (by positivity)]
        rw [sq_sqrt (by positivity), sq_sqrt (by positivity)]
        rw [sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_mul (by positivity)]
        ring
      _ = _ := by
        rw [sqrt_sq (by positivity)]
  have h2 (n : ℕ) : √(as (n + 1) + 1) = √(a + 1) * √(as n + 1) + √a * √(as n) := by
    calc
      _ = √((√(a + 1) * √(as n + 1) + √a * √(as n)) ^ 2) := by
        have := as_nonneg (n := n)
        rw [h_an]
        congr
        rw [add_sq, mul_pow, mul_pow, sq_sqrt as_nonneg, sq_sqrt (by positivity)]
        rw [sq_sqrt (by positivity), sq_sqrt (by positivity)]
        rw [sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_mul (by positivity)]
        ring
      _ = _ := by
        rw [sqrt_sq (by positivity)]
  -- From these we obtain recursions:
  have hrecm (n : ℕ) : √(as (n + 1) + 1) - √(as (n + 1)) = (√(a + 1) - √a) * (√(as n + 1) - √(as n)) := by
    rw [h2, h1]
    ring
  have hrecp (n : ℕ) : √(as (n + 1) + 1) + √(as (n + 1)) = (√(a + 1) + √a) * (√(as n + 1) + √(as n)) := by
    rw [h2, h1]
    ring
  -- By induction this implies:
  have hm (n : ℕ) : √(as n + 1) - √(as n) = (√(a + 1) - √a) ^ n := by
    induction' n with n ih
    · simp [h_a0]
    · rw [hrecm, ih]
      ring
  have hp (n : ℕ) : √(as n + 1) + √(as n) = (√(a + 1) + √a) ^ n := by
    induction' n with n ih
    · simp [h_a0]
    · rw [hrecp, ih]
      ring
  -- This gives a formula for `√(as n)`:
  have hsqrt_eq (n : ℕ) : √(as n) = (1 / 2) * ((√(a + 1) + √a) ^ n - (√(a + 1) - √a) ^ n) := by
    linarith only [hm n, hp n]
  -- -- Squaring this on both sides we get:
  have h_eq (n : ℕ) : as n = (1 / 4) * ((√(a + 1) + √a) ^ (2 * n) + (√(a + 1) - √a) ^ (2 * n) - 2) := by
    calc
      _ = (√(as n)) ^ 2 := by rw [sq_sqrt as_nonneg]
      _ = ((1 / 2) * ((√(a + 1) + √a) ^ n - (√(a + 1) - √a) ^ n)) ^ 2 := by rw [hsqrt_eq]
      _ = _ := by
        rw [mul_pow]
        congr! 1
        · norm_num
        · rw [sub_sq, ← pow_mul, ← pow_mul, mul_comm n 2]
          have : (√(a + 1) + √a) ^ n * (√(a + 1) - √a) ^ n = 1 := by
            rw [← mul_pow, ← sq_sub_sq, sq_sqrt (by positivity), sq_sqrt (by positivity)]
            ring
          rw [mul_assoc, this]
          ring
  -- By the binomial theorem we derive that this is indeed an integer. First:
  have h3 (n : ℕ) : (√(a + 1) + √a) ^ (2 * n) + (√(a + 1) - √a) ^ (2 * n)
      = 2 * ∑ j ∈ range (n + 1), (2 * n).choose (2 * j) * (a + 1) ^ j * a ^ (n - j) := by
    rw [add_pow, sub_pow]
    rw [← sum_filter_add_sum_filter_not (range (2 * n + 1)) (fun j ↦ j % 2 = 0)]
    rw [add_assoc]
    rw [← sum_filter_add_sum_filter_not (range (2 * n + 1)) (fun j ↦ j % 2 = 0)]
    conv =>
      enter [1, 2]
      conv =>
        enter [2]
        rw [add_comm (∑ _ ∈ _, _)]
      rw [← add_assoc, ← sum_add_distrib]
    rw [sum_eq_zero (s := filter (fun k : ℕ ↦ ¬k % 2 = 0) (range (2 * n + 1))), zero_add]
    rw [← sum_add_distrib]
    push_cast
    rw [mul_sum]
    apply sum_bij  (i := fun j _ ↦ j / 2)
    · intro j hj
      simp at hj
      simp
      omega
    · intro i hi j hj hij
      simp at hi
      simp at hj
      omega
    · intro j hj
      use 2 * j, ?_
      · omega
      · simp at hj
        simp
        omega
    · intro j hj
      simp at hj
      have hj' : j = 2 * (j / 2) := by omega
      have : (-1 : ℝ) ^ (j + 2 * n) = 1 := by
        rw [hj', ← mul_add]
        simp
      rw [this, one_mul, ← two_mul]
      rw [sqrt_eq_rpow, sqrt_eq_rpow, show 2 * (j / 2) = j by omega]
      have hpowcast {x : ℝ} {j : ℕ} : x ^ j = x ^ (j : ℝ) := by norm_cast
      rw [hpowcast, hpowcast, ← rpow_mul (by positivity), ← rpow_mul (by positivity)]
      have hcast1 : (1 : ℝ) / 2 * j = ↑(j / 2) := by
        nth_rewrite 1 [hj']
        simp
      have hcast2 : (1 : ℝ) / 2 * ↑(2 * n - j) = ↑(n - j / 2) := by
        nth_rewrite 1 [hj']
        rw [show 2 * n - 2 * (j / 2) = 2 * (n - j / 2) by omega]
        simp
      rw [hcast1, hcast2]
      simp
      ring
    · intro j hj
      simp at hj
      have hj' : j = 2 * (j / 2) + 1 := by omega
      have : (-1 : ℝ) ^ (j + 2 * n) = -1 := by
        rw [hj', add_comm _ 1, add_assoc, pow_add, ← mul_add]
        simp
      rw [this]
      simp
  -- This implies the claim
  intro n hn
  set m' := ∑ j ∈ range (n + 1), (2 * n).choose (2 * j) * (a + 1) ^ j * a ^ (n - j) with m'_eq
  set m := (m' - 1) / 2 with m_eq
  -- We need to show that `m'` is odd
  have hodd : m' = 2 * (m' / 2) + 1 := by
    suffices h : m' % 2 = 1 by omega
    by_cases ha' : a % 2 = 0
    · -- If `a` is even, then all summands are even except for `j = n`
      rw [m'_eq, sum_range_succ, Nat.add_mod, sum_nat_mod, sum_eq_zero, Nat.zero_mod, zero_add]
      · simp [Nat.pow_mod, Nat.add_mod, ha']
      · intro j hj
        simp at hj
        have : n - j ≠ 0 := by omega
        rw [Nat.mul_mod, Nat.pow_mod, ha', zero_pow (by assumption)]
        simp
    · -- If `a` is odd, then all summands are even except for `j = 0`
      replace ha' : a % 2 = 1 := by omega
      rw [m'_eq, sum_range_succ', Nat.add_mod, sum_nat_mod, sum_eq_zero, Nat.zero_mod, zero_add]
      · simp [Nat.pow_mod, Nat.add_mod, ha']
      · intro j hj
        simp at hj
        rw [Nat.mul_mod, Nat.mul_mod _ (_ ^ _), Nat.pow_mod, Nat.add_mod, ha']
        simp
  use m
  have : as n = m := by
    rw [h_eq, h3, ← m'_eq, m_eq]
    have : (2 : ℝ) * m' - 2  = ↑(4 * (m' / 2)) := by
      nth_rewrite 1 [hodd]
      push_cast
      ring
    rw [this]
    nth_rewrite 2 [hodd]
    simp
  constructor
  · suffices h : 0 < (m : ℝ) by exact_mod_cast h
    rw [← this]
    exact as_pos hn
  · assumption
