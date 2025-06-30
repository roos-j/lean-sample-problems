import Mathlib

open Finset Complex Polynomial Function

/- Let $f(x)$ be a polynomial with complex coefficients, $f(x) \neq x$,

$$f_{(x)}^{(n)}=\underbrace{f(f(\cdots(f(x))}_{n \in} \cdots)), F_{n}(x)=f^{(n)}(x)-x, n \in \mathrm{N}.$$

Prove: $(f(x)-x) \mid F_{n}(x)$. -/
theorem algebra_266734 {f : Polynomial ℂ} (hf : f ≠ X) :
    ∀ n : ℕ, (f - X) ∣ f.comp^[n] (X) - X := by
  -- We proceed by induction on `n`
  intro n
  induction' n with n ih
  · -- The claim is clear when `n=0`
    simp
  · -- Suppose the claim holds for `n`; let us prove it for `n+1`
    obtain ⟨g, hg⟩ := ih
    rw [add_comm, iterate_add, iterate_one, comp_apply]
    -- By inductive hypothesis and adding and subtacting `f.comp^[n] X` it suffices to prove:
    suffices h : (f - X) ∣ f.comp (f.comp^[n] X) - f.comp^[n] X by
      obtain ⟨q, hq⟩ := h
      use g + q
      linear_combination hg + hq
    -- Decompose `f - X` as a product of linear polynomials.
    have e1 := eq_prod_roots_of_splits <| isAlgClosed.splits <| f - X
    simp only [map_sub, map_id, map_X, RingHom.id_apply] at e1
    -- Substituting `f.comp^[n] X` for `X` in `e1` we get
    have e2 : f.comp (f.comp^[n] X) - f.comp^[n] X = C (f - X).leadingCoeff * (Multiset.map (fun x => f.comp^[n] X - C x) (f - X).roots).prod := by
      nth_rewrite 2 [← X_comp (p := f.comp^[n] X)]
      rw [← sub_comp]
      nth_rewrite 1 [e1]
      rw [mul_comp, C_comp, multiset_prod_comp]
      simp only [Multiset.map_map, comp_apply, sub_comp, X_comp, C_comp]
    have ne_zero : f - X ≠ 0 := by
      by_contra h
      exact False.elim <| hf (by linear_combination h)
    -- This implies that `f.comp (f.comp^[n] X) - f.comp^[n] X` vanishes at roots of `f - X`, which gives the claim
    rw [e1, e2]
    apply (C_mul_dvd <| leadingCoeff_ne_zero.mpr ne_zero).mpr
    apply (dvd_C_mul <| leadingCoeff_ne_zero.mpr ne_zero).mpr
    refine Multiset.prod_dvd_prod_of_dvd _ _ ?_
    intro r hr
    rw [mem_roots ne_zero] at hr
    apply dvd_iff_isRoot.mpr
    unfold IsRoot
    rw [show eval r (f.comp^[n] X - C r) = eval r (f.comp^[n] X - X) by simp, hg, eval_mul]
    apply mul_eq_zero_of_left hr
