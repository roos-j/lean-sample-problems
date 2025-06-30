import Mathlib

/- The sequences of positive integers
$1,a_2, a_3,...$ and $1,b_2, b_3,...$ are an increasing arithmetic sequence and an increasing geometric sequence, respectively.
Let $c_n=a_n+b_n$​. There is an integer $k$ such that $c_{k-1}=100$ and $c_{k+1}=1000$. Find $c_k$​.
-/
theorem algebra_96923 {a b : ℕ → ℕ} {α β : ℕ} (ha : ∀ n, a n = 1 + α * n)
    (hb : ∀ n, b n = β ^ n) (c : ℕ → ℕ) (hc : ∀ n, c n = a n + b n) :
    ∃ k, c (k - 1) = 100 ∧ c (k + 1) = 1000 → c k = 262 := by
  -- Note that we have chosen to move the existence of `k` into the hypothesis instead of leaving it as an assumption.
  -- This still captures the mathematical content of the problem and is convenient for formalization.
  -- Trying different cases for `k` it turns out that `k = 2` works (and it is the only one, but we don't need to show that)
  use 2
  rintro ⟨hc₁, hc₂⟩
  -- Plugging this into the equations for `c` gives two equations for `α, β`
  have e1 : (100 : ℤ) = 1 + α + β := by
    calc _ = (c 1 : ℤ) := by rw [hc₁]; norm_cast
          _ = 1 + α + β := by rw [hc 1, ha 1, hb 1, mul_one, pow_one]; norm_cast
  have e2 : (1000 : ℤ) = 1 + α * 3 + β ^ 3 := by
    calc _ = (c 3 : ℤ) := by rw [hc₂]; norm_cast
          _ = 1 + α * 3 + β ^ 3 := by rw [hc 3, ha 3, hb 3]; norm_cast
  -- Subtracting three times the first from the second equation
  have e3 : (β : ℤ) ^ 3 - β * 3 - 2 = 700 := by
    calc
      _ = (1000 : ℤ) - 100 * 3 := by rw [e1, e2]; linear_combination
      _ = 700 := by rfl
  -- Rearranging gives the following
  have e4 : (β : ℤ) * (β ^ 2 - 3) = 702 := by linarith only [e3]
  -- The only natural number solution to this is `β = 9` (this is obvious from looking at factors of `702`)
  have β_eq : β = 9 := by
    have h : ∀ β : ℕ, β ≤ 100 → (β : ℤ) * (β ^ 2 - 3) = 702 → β = 9 := by decide -- `decide` is okay here because this step is informally trivial
    have : β ≤ 100 := by
      calc
        _  ≤ 1 + α + β := by linarith only
        _  = c 1 := by linarith only [ha 1, hb 1, hc 1]
        _  = 100 := hc₁
    exact h β this e4
  -- This implies `α = 90` and thus `c 2 = 262` as claimed
  have α_eq : α = 90 := by linarith only [ha 1, hb 1, hc 1, hc₁, β_eq]
  calc
    _ = a 2 + b 2 := hc 2
    _ = 1 + α * 2 + β ^ 2 := by rw [ha 2, hb 2]
    _ = 262 := by rw [α_eq, β_eq]; rfl
