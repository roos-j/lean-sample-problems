import Mathlib

open Complex

/- If $A=\left\{z \mid z^{18}=1\right\},
  B=\left\{w \mid w^{48}=1\right\}$, then
  the set $C=\{z w \mid z \in A, w \in B\}$ contains exactly 144 elements. -/
theorem number_theory_280455 {A B : Set ℂˣ} (hA : A = {z | z ^ 18 = 1}) (hB : B = {w | w ^ 48 = 1})
  (C : Set ℂˣ) (hC : C = {x | ∃ z ∈ A, ∃ w ∈ B, x = z * w}) :
    C.ncard = 144 := by
  -- It suffices to show that `C` is the set of `144`th roots of unity
  suffices h : C = {u | u ^ 144 = 1} by
    rw [h]
    change (rootsOfUnity 144 ℂ : Set ℂˣ).ncard = 144
    convert card_rootsOfUnity 144
    -- This goal should be simple, but due to some missing coercions in Mathlib, we have to suffer a little
    have : Fintype (rootsOfUnity 144 ℂ : Set ℂˣ) := by -- Manually coerce `rootsOfUnity.fintype`
      refine Fintype.ofEquiv (rootsOfUnity 144 ℂ) ⟨fun z ↦ z, fun z ↦ z, ?_, ?_⟩
        <;> exact fun _ ↦ by simp
    rw [Fintype.card_of_subtype (s := (rootsOfUnity 144 ℂ : Set ℂˣ).toFinset)]
    · exact Set.ncard_eq_toFinset_card' _
    · simp only [Set.mem_toFinset, SetLike.mem_coe, implies_true]
  rw [hC]
  ext x
  constructor
  · -- Let `x ∈ C`. Then there exist `z ∈ A, w ∈ B` with `x = z * w`:
    rintro ⟨z, ⟨hzA, w, ⟨hwB, hx⟩⟩⟩
    -- We need to show `x ^ 144 = 1`. This follows by the assumptions:
    calc
      _ = (z * w) ^ 144 := by rw [hx]
      _ = (z ^ 18) ^ 8 * (w ^ 48) ^ 3 := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
      _ = _ := by
        rw [hA] at hzA
        rw [hB] at hwB
        rw [hzA, hwB]
        norm_num
  · -- Conversely, let `x` be a 144th root of unity. We need to show that `x ∈ C`
    intro hx
    -- Then `x` takes the form `exp (2 * pi * I * k / 144)` for some natural `k < 144`
    obtain ⟨k, ⟨hk, hk'⟩⟩ := (Complex.mem_rootsOfUnity 144 x).mp hx
    -- Exploiting that `8` and `3` are coprime we write:
    -- We may use `z = exp (-2 * pi * I * k / 18)` and `w = exp (2 * pi * I * 3 * k / 48)`
    let z := exp (-2 * Real.pi * I * (k / 18))
    let w := exp (2 * Real.pi * I * (3 * k / 48))
    use Units.mk0 z (by simp [z])
    constructor
    · -- We calculate that indeed `z ^ 18 = 1`
      rw [hA]
      ext
      simp [z]
      rw [← exp_nat_mul, exp_eq_one_iff]
      use -k
      field_simp
      ring
    · use Units.mk0 w (by simp [w])
      constructor
      · -- We calculate that `w ^ 48 = 1`
        rw [hB]
        ext
        simp [w]
        rw [← exp_nat_mul, exp_eq_one_iff]
        use 3 * k
        field_simp
        ring
      · -- We calculate that `x = z * w`
        ext
        simp [z, w]
        rw [← hk', ← exp_add]
        congr
        field_simp
        ring
