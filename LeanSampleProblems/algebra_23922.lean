import Mathlib

open Function

/- Suppose that $f$ and $g$ are two functions defined on the set of positive integers and taking positive integer values.
   Suppose also that the equations $f(g(n))=f(n)+1$ and $g(f(n))=$ $g(n)+1$ hold for all positive integers.
   Prove that $f(n)=g(n)$ for all positive integer $n$. (Germany) -/
theorem algebra_23922 {f g : ℕ → ℕ} (hf : ∀ n > 0, 0 < f n) (hg : ∀ n > 0, 0 < g n)
    (h1 : ∀ n > 0, f (g n) = f n + 1) (h2 : ∀ n > 0, g (f n) = g n + 1) :
    ∀ n > 0, f n = g n := by
  -- First, by repeated application of `h1`
  have h3 (k : ℕ) (x : ℕ) (hx : 0 < x) : f (g^[k] x) = f x + k := by
    induction' k with k ih generalizing x
    · simp
    · rw [iterate_succ, comp_apply, ih _ (hg _ hx), h1 _ hx]
      ring
  -- Similarly, by repeated application of `h2`
  have h4 (k : ℕ) (x : ℕ) (hx : 0 < x) : g (f^[k] x) = g x + k := by
    induction' k with k ih generalizing x
    · simp
    · rw [iterate_succ, comp_apply, ih _ (hf _ hx), h2 _ hx]
      ring
  -- Let `a` be the minimum value of `f` attained at `nf`; and `b` the minimum value of `g` attained at `ng`
  obtain ⟨a, ⟨nf, nf_pos, hnf⟩, ha⟩ := wellFounded_lt.has_min (f '' {n | 0 < n}) (by use f 1; use 1; simp)
  obtain ⟨b, ⟨ng, ng_pos, hng⟩, hb⟩ := wellFounded_lt.has_min (g '' {n | 0 < n}) (by use g 1; use 1; simp)
  simp only [Set.mem_image, Set.mem_setOf_eq, not_lt, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at ha hb
  -- Auxiliary positivity claims
  have g_it_nf_pos {d : ℕ} : 0 < g^[d] nf := by
    induction' d with d ih
    · exact nf_pos
    · rw [add_comm, iterate_add, iterate_one, comp_apply]
      exact hg _ ih
  have f_it_ng_pos {d : ℕ} : 0 < f^[d] ng := by
    induction' d with d ih
    · exact ng_pos
    · rw [add_comm, iterate_add, iterate_one, comp_apply]
      exact hf _ ih
  have a_pos : 0 < a := by
    rw [← hnf]
    exact hf _ nf_pos
  have b_pos : 0 < b := by
    rw [← hng]
    exact hg _ ng_pos
  -- Then every value of `f` can be written as `a + d`
  have hrangef {x : ℕ} (hx : 0 < x) : ∃ d, f x = a + d := by
    have := ha _ hx
    use (f x - a)
    exact Eq.symm (Nat.add_sub_of_le this)
  -- Moreover, if `x ≥ a`, then `x` is a value of `f`
  have exists_of_a_le {x : ℕ} (hx : a ≤ x) : ∃ y, 0 < y ∧ f y = x := by
    use g^[x - a] nf
    constructor
    · exact g_it_nf_pos
    · rw [h3 _ nf nf_pos, hnf]
      exact Nat.add_sub_of_le hx
  -- Analogously for g
  have exists_of_b_le {x : ℕ} (hx : b ≤ x) : ∃ y, 0 < y ∧ g y = x := by
    use f^[x - b] ng
    constructor
    · exact f_it_ng_pos
    · rw [h4 _ ng ng_pos, hng]
      exact Nat.add_sub_of_le hx
  -- Claim 1.1: `f x = f y` iff `g x = g y`
  have feq_iff_geq {x y : ℕ} (hx : 0 < x) (hy : 0 < y) : f x = f y ↔ g x = g y := by
    -- This follows by applying the original functional equations
    constructor
    · intro h
      calc
        _ = g (f x) - 1 := by
          specialize h2 x
          specialize hg (f x) (hf x hx)
          clear * - h2 hg hx
          omega
        _ = g (f y) - 1 := by congr
        _ = _ := by
          specialize h2 y
          specialize hg (f y) (hf y hy)
          clear * - h2 hg hy
          omega
    · intro h
      calc
        _ = f (g x) - 1 := by
          specialize h1 x
          specialize hf (g x) (hg x hx)
          clear * - h1 hf hx
          omega
        _ = f (g y) - 1 := by congr
        _ = _ := by
          specialize h1 y
          specialize hf (g y) (hg y hy)
          clear * - h1 hf hy
          omega
  -- Claim 1.2: If `f (f x) = f (f y)`, then `f x = f y`
  have feq_of_ffeq {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hffeq : f (f x) = f (f y)) : f x = f y := by
    -- By Claim 1.1:
    have : g (f x) = g (f y) := (feq_iff_geq (hf x hx) (hf y hy)).mp hffeq
    -- Then by the functional equation:
    have : g x = g y := by
      rw [h2 _ hx, h2 _ hy] at this
      linarith only [this]
    -- We are done by again applying Claim 1.1
    exact (feq_iff_geq hx hy).mpr this
  -- Claim 1.2': Version for `g`
  have geq_of_ggeq {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hggeq : g (g x) = g (g y)) : g x = g y := by
    have := (feq_iff_geq (hg x hx) (hg y hy)).mpr hggeq
    have : f x = f y := by
      rw [h1 _ hx, h1 _ hy] at this
      linarith only [this]
    exact (feq_iff_geq hx hy).mp this
 -- Claim 1.3: If `f x = f y` and `x, y` are both `≥ a`, then `x = y`
  have eq_of_f_eq_f {x y : ℕ} (hx : a ≤ x) (hy : a ≤ y) (hxy : f x = f y) : x = y := by
    -- We know that `x, y` are images of `f`
    obtain ⟨x', x'_pos, hx'⟩ := exists_of_a_le hx
    obtain ⟨y', y'_pos, hy'⟩ := exists_of_a_le hy
    rw [← hx', ← hy']
    -- Then we can apply Claim 1.2
    apply feq_of_ffeq x'_pos y'_pos
    rw [hx', hy']
    exact hxy
  -- Analogously for `g`
  have eq_of_g_eq_g {x y : ℕ} (hx : b ≤ x) (hy : b ≤ y) (hxy : g x = g y) : x = y := by
    obtain ⟨x', x'_pos, hx'⟩ := exists_of_b_le hx
    obtain ⟨y', y'_pos, hy'⟩ := exists_of_b_le hy
    rw [← hx', ← hy']
    apply geq_of_ggeq x'_pos y'_pos
    rw [hx', hy']
    exact hxy
  -- Claim 2.1: If `f x = a`, then `x < b`; analogous for `g`
  have lt_b_of_f_eq_a {x : ℕ} (hx : 0 < x) (hx' : f x = a) : x < b := by
    -- Suppose `b ≤ x`
    by_contra! h
    -- Then `x` is an image of `g`
    obtain ⟨y, y_pos, hy⟩ := exists_of_b_le h
    -- This gives a contradiction
    suffices h : a + 1 ≤ a by omega
    calc
      _ ≤ f y + 1 := by gcongr; exact ha _ y_pos
      _ = f (g y) := (h1 _ y_pos).symm
      _ = _ := by rwa [hy]
  -- Claim 2.1': Version for `g`
  have lt_a_of_g_eq_b {x : ℕ} (hx : 0 < x) (hx' : g x = b) : x < a := by
    by_contra! h
    obtain ⟨y, y_pos, hy⟩ := exists_of_a_le h
    suffices h : b + 1 ≤ b by omega
    calc
      _ ≤ g y + 1 := by gcongr; exact hb _ y_pos
      _ = g (f y) := (h2 _ y_pos).symm
      _ = _ := by rwa [hy]
  -- Claim 2.2: If `y < b` whenever `f x = f y`, then `f x = a`
  have f_eq_a_of {x : ℕ} (hx : 0 < x) (hx' : ∀ y > 0, f x = f y → y < b) : f x = a := by
    -- If not, then `f x > a`
    by_contra! h
    have : a < f x := by
      have := ha _ hx
      exact Nat.lt_of_le_of_ne this <| id <| Ne.symm h
    -- Then there is `y` so that `f y = f x - 1`
    obtain ⟨y, y_pos, hy⟩ := exists_of_a_le <| (Nat.le_sub_one_iff_lt (hf _ hx)).mpr this
    -- Then by the functional equation:
    have : f (g y) = f x := by
      rw [h1 _ y_pos]
      clear * - this hy
      omega
    -- Then `g y < b` by assumption, which is a contradiction
    specialize hx' _ (hg _ y_pos) this.symm
    have := hb _ y_pos
    clear * - hx' this
    omega
  -- Claim 2.2': Analogous version
  have g_eq_b_of {x : ℕ} (hx : 0 < x) (hx' : ∀ y > 0, g x = g y → y < a) : g x = b := by
    by_contra! h
    have : b < g x := by
      have := hb _ hx
      exact Nat.lt_of_le_of_ne this <| id <| Ne.symm h
    obtain ⟨y, y_pos, hy⟩ := exists_of_b_le <| (Nat.le_sub_one_iff_lt (hg _ hx)).mpr this
    have : g (f y) = g x := by
      rw [h2 _ y_pos]
      clear * - this hy
      omega
    specialize hx' _ (hf _ y_pos) this.symm
    have := ha _ y_pos
    clear * - hx' this
    omega
  -- Contraposed versions of Claim 2.2
  have exists_b_le_of {x : ℕ} (hx : 0 < x) (hx' : a < f x) : ∃ y > 0, f x = f y ∧ b ≤ y := by
    have := f_eq_a_of hx
    contrapose! this
    exact ⟨this, ne_of_gt hx'⟩
  have exists_a_le_of {x : ℕ} (hx : 0 < x) (hx' : b < g x) : ∃ y > 0, g x = g y ∧ a ≤ y := by
    have := g_eq_b_of hx
    contrapose! this
    exact ⟨this, ne_of_gt hx'⟩
  -- Claim 2.3: `g nf = g ng = b`
  have g_nf_eq : g nf = b := by
    obtain hab | hab := Nat.le_total b a
    · -- Suppose `b ≤ a`. Then we apply Claim 2.2':
      apply g_eq_b_of nf_pos
      intro y hy h
      have := (feq_iff_geq nf_pos hy).mpr h
      rw [hnf] at this
      -- Then `y < b` by Claim 2.1, which shows the claim since `b ≤ a`
      have := lt_b_of_f_eq_a hy this.symm
      exact Trans.trans this hab
    · -- The other direction follows analogously
      suffices h : f ng = a by
        rw [← hnf] at h
        rw [← hng]
        exact (feq_iff_geq nf_pos ng_pos).mp h.symm
      apply f_eq_a_of ng_pos
      intro y hy h
      have := (feq_iff_geq ng_pos hy).mp h
      rw [hng] at this
      have := lt_a_of_g_eq_b hy this.symm
      exact Trans.trans this hab
  -- Similarly, for `f`:
  have f_ng_eq : f ng = a := by
    rw [← hnf]
    have := (feq_iff_geq ng_pos nf_pos).mpr
    rw [hng] at this
    exact this g_nf_eq.symm
  -- Claim 3.1: `a < f a`
  have a_lt_f_a : a < f a := by
    -- Suppose not, then `f a = a`
    by_contra! h
    have := le_antisymm h <| ha a a_pos
    -- We will establish a contradiction to Claim 2.1 for `g` with `x = a`
    nth_rewrite 2 [← hnf] at this
    have : g a = g nf := (feq_iff_geq a_pos nf_pos).mp this
    -- By Claim 2.3:
    rw [g_nf_eq] at this
    -- Then by Claim 2.1, `a < a`, contradiction:
    have := lt_a_of_g_eq_b a_pos this
    exact (lt_self_iff_false _).mp this
  -- Analogously for `g`:
  have b_lt_g_b : b < g b := by
    -- Suppose not, then `f a = a`
    by_contra! h
    have := le_antisymm h <| hb b b_pos
    -- We will establish a contradiction to Claim 2.1 for `f` with `x = b`
    nth_rewrite 2 [← hng] at this
    have := (feq_iff_geq b_pos ng_pos).mpr this
    -- By Claim 2.3:
    rw [f_ng_eq] at this
    -- Then by Claim 2.1, `a < a`, contradiction:
    have := lt_b_of_f_eq_a b_pos this
    exact (lt_self_iff_false _).mp this
  -- Claim 3.2: `a = b`
  have a_eq_b : a = b := by
    apply le_antisymm
    · -- Since `b < g b` there is `b'` with `g b = g b'` and `a ≤ b'`
      obtain ⟨b', _, hb', hab'⟩ := exists_a_le_of b_pos b_lt_g_b
      -- Then `b' ≤ b`, because otherwise we get a contradiction to Claim 1.3
      have : b' ≤ b := by
        by_contra! h
        have := eq_of_g_eq_g le_rfl (le_of_lt h) hb'
        rw [this] at h
        exact (lt_self_iff_false _).mp h
      exact Trans.trans hab' this
    · -- By the same argument:
      obtain ⟨a', _, ha', hab'⟩ := exists_b_le_of a_pos a_lt_f_a
      have : a' ≤ a := by
        by_contra! h
        have := eq_of_f_eq_f le_rfl (le_of_lt h) ha'
        rw [this] at h
        exact (lt_self_iff_false _).mp h
      exact Trans.trans hab' this
  -- Claim 4: `f^[d + 1] (nf) = a + d` and the same for `g`
  have g_it_succ_nf_eq {d : ℕ} : g^[d + 1] nf = a + d ∧ f^[d + 1] nf = a + d := by
    -- This follows by induction on `d` and Claims 2.3, 3
    induction' d with d ih
    · rw [zero_add, iterate_one, add_zero]
      constructor
      · rw [a_eq_b]
        exact g_nf_eq
      · exact hnf
    · have ih' : f^[d + 1] nf = g^[d+1] nf := Eq.trans ih.2 ih.1.symm
      constructor
      · rw [add_comm, iterate_add, iterate_one, comp_apply, ← ih']
        rw [h4 _ _ nf_pos, g_nf_eq, a_eq_b]
      · rw [add_comm, iterate_add, iterate_one, comp_apply, ih']
        rw [h3 _ _ nf_pos, hnf]
  -- Now the claim follows from Claim 4, `hrangef` and `feq_iff_geq`
  intro x hx
  obtain ⟨d, hd⟩ := hrangef hx
  have hfeq : f x = f (g^[d] nf) := by
    rw [hd, ← hnf]
    exact (h3 d nf nf_pos).symm
  symm
  calc
    _ = g (g^[d] nf) := (feq_iff_geq hx g_it_nf_pos).mp hfeq
    _ = a + d := by
      rw [← g_it_succ_nf_eq.1, add_comm, iterate_add, iterate_one, comp_apply]
    _ = _ := hd.symm
