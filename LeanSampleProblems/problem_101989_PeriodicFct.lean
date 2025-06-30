import Mathlib

/- Let functions $f(x)$ and $g(y)$ be defined on the set of real numbers $\mathbf{R}$, and $f(0)=1, g(a)=1$ where $a\not=0$.
Suppose $g(x)$ is an odd function and $f(x-y)=f(x) f(y)+g(x) g(y)$.
Prove: The function $f(x)$ is a periodic function. -/
theorem algebra_101989 {f g : ℝ → ℝ} {a : ℝ} -- (ha : a ≠ 0)
    (hf0 : f 0 = 1) (hga : g a = 1)
    (hodd : Function.Odd g) (hfg : ∀ x y, f (x - y) = f x * f y + g x * g y) :
    ∃ c, Function.Periodic f c := by
  -- Substituting `x = y = 0` into the equation gives
  have hg0 : g 0 = 0 := by
    specialize hfg 0 0
    rw [sub_self, hf0] at hfg
    simp at hfg
    exact hfg
  -- Substituting `x = y = a` gives
  have hfa : f a = 0 := by
    specialize hfg a a
    rw [sub_self, hf0, hga] at hfg
    simp at hfg
    exact hfg
  -- Substituting `x = 0, y = a` gives
  have hfnega : f (-a) = 0 := by
    specialize hfg 0 a
    rw [zero_sub, hf0, hfa, hg0, hga] at hfg
    simp at hfg
    exact hfg
  -- Substituting `y = a` and `y = -a` respectively gives:
  have e1 (x : ℝ) : f (x - a) = g x := by
    specialize hfg x a
    rw [hfa, hga] at hfg
    simp at hfg
    exact hfg
  have e2 (x : ℝ) : f (x + a) = - g x := by
    specialize hfg x (-a)
    rw [hfnega, hodd, hga] at hfg
    simp at hfg
    exact hfg

  -- Adding `e1` and `e2` gives
  have e3 (x : ℝ) : f (x + a) + f (x - a) = 0 := by rw [e1, e2]; group

  -- Replacing `x` by `x + 2 * a` in this gives
  have e4 (x : ℝ) : f (x + 3 * a) + f (x + a) = 0 := by rw [← e3 (x + 2 * a)]; group

  -- The last two equations imply:
  have e5 (x : ℝ) : f (x + 3 * a) = f (x - a) := by linear_combination (e4 x) - (e3 x)

  -- Replacing `x` by `x + a` in this gives that `f` is 4-periodic
  use 4 * a
  intro x
  calc
    _ = f ((x + a) + 3 * a) := by group
    _ = f ((x + a) - a) := e5 _
    _ = _ := by group
