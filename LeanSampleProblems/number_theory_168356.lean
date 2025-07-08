import Mathlib

open ZMod

/-
  24. $[\mathbf{1 2}]$ At a recent math contest, Evan was asked to find $2^{2016}(\bmod p)$ for a given prime number $p$ with $100 < p < 500$.

  Evan has forgotten what the prime $p$ was, but still remembers how he solved it:

   Evan first tried taking 2016 modulo $p-1$, but got a value $e$ larger than 100 .

   However, Evan noted that $e-\frac{1}{2}(p-1)=21$, and then realized the answer was $-2^{21}(\bmod p)$.

  What was the prime $p$ ? -/
theorem number_theory_168356 (p : ℕ) (hp : Nat.Prime p) (h : 100 < p ∧ p < 500)
    (e : ℕ) (he : e = 2016 % (p - 1)) (h1 : e > 100) (h2 : (e : ℤ) - (p - 1) / 2 = 21)
    (h3 : (2 : ZMod p) ^ 2016 = -2 ^ 21):
    p = 211 := by
  -- This could be shortened significantly by `interval_cases` / `omega` but we follow a more plausible human reasoning path
  have : Fact (Nat.Prime p) := ⟨hp⟩
  -- Since `p` is an odd prime we can write it as `2 * d + 1`:
  obtain ⟨d, hd⟩ := hp.odd_of_ne_two (by omega)
  have two_nz : (2 : ZMod p) ≠ 0 := by -- extend `omega` to be able to do this
    intro h
    have := (eq_iff_modEq_nat p).mp <|
      (show (2 : ZMod p) = (2 : ℕ) by rfl) ▸
      show (0 : ZMod p) = (0 : ℕ) by simp ▸ h
    change 2 % p = 0 % p at this
    simpa [Nat.zero_mod _ ▸ this, show 2 / p = 0 from Nat.div_eq_of_lt (by omega)]
      using Nat.div_add_mod 2 p
  -- By the little Fermat theorem we must have:
  have h3' : (2 : ZMod p) ^ 2016 = 2 ^ e := by
    rw [← Nat.div_add_mod 2016 (p - 1), pow_add, pow_mul,
      pow_card_sub_one_eq_one (by assumption), one_pow, one_mul, he]
  -- By the assumption:
  have he_eq : e = d + 21 := by omega
  -- This implies:
  have hpowd : (2 : ZMod p) ^ d = -1 := by
    rw [h3', he_eq, pow_add, neg_eq_neg_one_mul] at h3
    apply mul_right_cancel₀ ?_ h3
    exact pow_ne_zero _ two_nz
  -- By Euler's criterion, we have `(2 / p) = -1`
  have hqr := (show p / 2 = d by omega) ▸ legendreSym.eq_pow p 2
  push_cast at hqr
  rw [hpowd] at hqr
  -- The assumptions imply `2016 = d + 1 (mod 2 * d)`
  have he' := he_eq ▸ show p - 1 = 2 * d by omega ▸ he
  -- This implies that `d` divides 1995
  have hd_dvd : d ∣ 1995 := by -- `omega` can't do it
    have := he' ▸ Nat.div_add_mod 2016 (2 * d)
    use (2 * (2016 / (2 * d))) + 1
    nth_rewrite 3 [← mul_one d] at this
    nth_rewrite 1 [mul_comm 2] at this
    rw [mul_assoc, ← add_assoc, ← mul_add] at this
    exact add_right_cancel (b := 21) this.symm
  -- Since `100 < p` and `p < 500` we have:
  have hd1 : 50 < d := by omega
  have hd2 : d < 250 := by omega
  -- This leaves only `4` options for `d`:
  have hd_eq : d = 57 ∨ d = 95 ∨ d = 105 ∨ d = 133 := by
    clear * - hd_dvd hd1 hd2
    interval_cases d <;> omega
  -- This only leaves two options for `p`
  have hp_eq : p = 191 ∨ p = 211 := by
    rw [hd] at hp ⊢
    clear * - hp hd_eq
    rcases hd_eq with h | h | h | h
      <;> {
        rw [h] at hp ⊢
        norm_num at hp ⊢ }
  rcases hp_eq with hp | hp
  · -- It can't be `p = 191` because `(2 / 191) = 1`
    have : Fact (Nat.Prime 191) := ⟨by norm_num⟩
    have : legendreSym 191 2 = 1 := by
      rw [legendreSym.at_two (by omega)]
      decide
    simp_rw [hp, this] at hqr
    norm_num at hqr
    have : Fact (2 < p) := ⟨by simp [hp]⟩
    exact False.elim
      <| ZMod.neg_one_ne_one (n := p) hqr.symm
  · -- This only leaves `p = 211`
    assumption
