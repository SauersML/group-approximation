import Mathlib.Logic.Equiv.Basic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Conjugation

/-!
# The Weyl relation `w x_kl(a) w⁻¹ = x_{τk τl}(λ(k) a ρ(l))` in `St_I(R)`

Lane `sk-rows-11`.  For `i ≠ j`, `u : Rˣ`, `τ = Equiv.swap i j`, define the left and right
multipliers

* `weylLeft i j u k = -u⁻¹` if `k = i`, `u` if `k = j`, `1` otherwise;
* `weylRight i j u l = -u` if `l = i`, `u⁻¹` if `l = j`, `1` otherwise.

These are the entries `W_{τk, k}` and `(W⁻¹)_{l, τl}` of the Weyl matrix
`W = u E_ij - u⁻¹ E_ji + Σ_{m ∉ {i,j}} E_mm` and its inverse, so matrix-wise
`W (1 + a E_kl) W⁻¹ = 1 + (W_{τk,k} a W⁻¹_{l,τl}) E_{τk τl}`.  The theorem `w_conj_x` proves the
corresponding identity in the Steinberg group for every root `(k, l)` with `{k, l} ≠ {i, j}`,
by dispatching to the five case lemmas of `SteinbergWeyl/Conjugation.lean`.

The excluded roots `(i, j)` and `(j, i)` are not claimed here (the lane target excludes them).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

open GroupApproximation.SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The left Weyl multiplier `W_{τk, k}`. -/
def weylLeft (i j : I) (u : Rˣ) (k : I) : R :=
  if k = i then -((u⁻¹ : Rˣ) : R) else if k = j then (u : R) else 1

/-- The right Weyl multiplier `(W⁻¹)_{l, τl}`. -/
def weylRight (i j : I) (u : Rˣ) (l : I) : R :=
  if l = i then -(u : R) else if l = j then ((u⁻¹ : Rˣ) : R) else 1

/-- **Weyl relation in `St_I(R)`.**  For `i ≠ j`, a unit `u`, and a root `(k, l)` other than
`(i, j)` and `(j, i)`, conjugation by `w_ij(u)` sends `x_kl(a)` to
`x_{τk, τl}(weylLeft k · a · weylRight l)`, where `τ = swap i j`. -/
theorem w_conj_x (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ¬(k = i ∧ l = j)) (hne' : ¬(k = j ∧ l = i)) (u : Rˣ) (a : R) :
    w i j hij u * x k l hkl a * (w i j hij u)⁻¹ =
      x (Equiv.swap i j k) (Equiv.swap i j l) ((Equiv.swap i j).injective.ne hkl)
        (weylLeft i j u k * a * weylRight i j u l) := by
  by_cases hki : k = i
  · have hli : l ≠ i := fun e => hkl (hki.trans e.symm)
    have hlj : l ≠ j := fun e => hne ⟨hki, e⟩
    rw [x_congr hkl hli.symm hki rfl rfl, w_conj_x_row_i i j l hij hli.symm hlj.symm u a]
    apply x_congr
    · rw [hki, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
    · rw [weylLeft, weylRight, if_pos hki, if_neg hli, if_neg hlj, mul_one]
  by_cases hkj : k = j
  · have hlj : l ≠ j := fun e => hkl (hkj.trans e.symm)
    have hli : l ≠ i := fun e => hne' ⟨hkj, e⟩
    rw [x_congr hkl hlj.symm hkj rfl rfl, w_conj_x_row_j i j l hij hli.symm hlj.symm u a]
    apply x_congr
    · rw [hkj, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
    · rw [weylLeft, weylRight, if_neg hki, if_pos hkj, if_neg hli, if_neg hlj, mul_one]
  by_cases hli : l = i
  · rw [x_congr hkl hki rfl hli rfl, w_conj_x_col_i i j k hij hki hkj u a]
    apply x_congr
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    · rw [hli, Equiv.swap_apply_left]
    · rw [weylLeft, weylRight, if_neg hki, if_neg hkj, if_pos hli, one_mul, mul_neg]
  by_cases hlj : l = j
  · rw [x_congr hkl hkj rfl hlj rfl, w_conj_x_col_j i j k hij hki hkj u a]
    apply x_congr
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    · rw [hlj, Equiv.swap_apply_right]
    · rw [weylLeft, weylRight, if_neg hki, if_neg hkj, if_neg hli, if_pos hlj, one_mul]
  rw [w_conj_x_disjoint i j k l hij hkl (Ne.symm hki) (Ne.symm hkj) (Ne.symm hli)
    (Ne.symm hlj) u a]
  apply x_congr
  · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
  · rw [weylLeft, weylRight, if_neg hki, if_neg hkj, if_neg hli, if_neg hlj, one_mul,
      mul_one]

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_conj_x
