import Mathlib.Data.Fintype.Card
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Weyl.Conjugation
import GroupApproximation.Meta.AxiomGuard

/-!
# Weyl conjugation of every root: `w_ij x_kl(c) w_ij⁻¹ = x_{σk, σl}(c)` (lane sk-leavitt-01)

Let `σ = swap i j`, and assume `2 = 0` in `R` and that a third index `m ∉ {i, j}` exists
(in `Fin n` this holds when `3 ≤ n`).

* Corner roots.  `x_ij(c) = ⁅x_im(c), x_mj(1)⁆`.  Conjugation respects commutators, so
  `w x_ij(c) w⁻¹ = ⁅x_jm(c), x_mi(1)⁆ = x_ji(c)`.  Symmetrically `w x_ji(c) w⁻¹ = x_ij(c)`.
  Both use the one-index cases of `LeavittK2.Weyl.Conjugation`.
* General `k ≠ l`.  Split into cases on `k ∈ {i, j}` and `l ∈ {i, j}`, and transport the
  indices with `WeylCalc.x_congr`.

Endpoint: `weyl_conj_x` (in `Fin n`, `3 ≤ n`), the lane statement.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open WeylCalc

/-- In `Fin n` with `3 ≤ n`, any two indices leave a third one. -/
theorem WeylCalc.exists_third {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ m : Fin n, m ≠ i ∧ m ≠ j := by
  have hcard : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨m, ?_, ?_⟩
  · rintro rfl
    simp at hm
  · rintro rfl
    simp at hm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc.exists_third

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- `w_ij x_ij(c) w_ij⁻¹ = x_ji(c)`, given a third index `m`, when `2 = 0`. -/
theorem weyl_conj_corner (h2 : (2 : R) = 0) (i j m : I) (hij : i ≠ j) (hmi : m ≠ i)
    (hmj : m ≠ j) (c : R) :
    weyl i j hij * x i j hij c * (weyl i j hij)⁻¹ = x j i hij.symm c := by
  have hx : x i j hij c = ⁅x i m hmi.symm c, x m j hmj (1 : R)⁆ := by
    rw [x_commutator i m j hmi.symm hmj hij, mul_one]
  rw [hx, conjugate_commutatorElement,
    weyl_conj_row_left h2 i j m hij hmi.symm hmj.symm c,
    weyl_conj_col_right h2 i j m hij hmi hmj 1,
    x_commutator j m i hmj.symm hmi hij.symm, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_corner

/-- `w_ij x_ji(c) w_ij⁻¹ = x_ij(c)`, given a third index `m`, when `2 = 0`. -/
theorem weyl_conj_corner_symm (h2 : (2 : R) = 0) (i j m : I) (hij : i ≠ j) (hmi : m ≠ i)
    (hmj : m ≠ j) (c : R) :
    weyl i j hij * x j i hij.symm c * (weyl i j hij)⁻¹ = x i j hij c := by
  have hx : x j i hij.symm c = ⁅x j m hmj.symm c, x m i hmi (1 : R)⁆ := by
    rw [x_commutator j m i hmj.symm hmi hij.symm, mul_one]
  rw [hx, conjugate_commutatorElement,
    weyl_conj_row_right h2 i j m hij hmi.symm hmj.symm c,
    weyl_conj_col_left h2 i j m hij hmi hmj 1,
    x_commutator i m j hmi.symm hmj hij, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_corner_symm

/-- **Weyl conjugation, general index type.**  If `2 = 0` and some index lies outside `{i, j}`,
then `w_ij x_kl(c) w_ij⁻¹ = x_{σk, σl}(c)` with `σ = swap i j`. -/
theorem weyl_conj_x_of_third (h2 : (2 : R) = 0) {i j : I} (hij : i ≠ j)
    (hthird : ∃ m : I, m ≠ i ∧ m ≠ j) (k l : I) (hkl : k ≠ l) (c : R) :
    weyl i j hij * x k l hkl c * (weyl i j hij)⁻¹ =
      x (Equiv.swap i j k) (Equiv.swap i j l) ((Equiv.swap i j).injective.ne hkl) c := by
  obtain ⟨m, hmi, hmj⟩ := hthird
  by_cases hki : k = i
  · by_cases hlj : l = j
    · rw [x_congr hki hlj hkl hij c, weyl_conj_corner h2 i j m hij hmi hmj c]
      exact x_congr (by rw [hki, Equiv.swap_apply_left])
        (by rw [hlj, Equiv.swap_apply_right]) _ _ c
    · have hil : i ≠ l := fun h => hkl (hki.trans h)
      have hjl : j ≠ l := fun h => hlj h.symm
      rw [x_congr hki rfl hkl hil c, weyl_conj_row_left h2 i j l hij hil hjl c]
      exact x_congr (by rw [hki, Equiv.swap_apply_left])
        (Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm).symm _ _ c
  · by_cases hkj : k = j
    · by_cases hli : l = i
      · rw [x_congr hkj hli hkl hij.symm c, weyl_conj_corner_symm h2 i j m hij hmi hmj c]
        exact x_congr (by rw [hkj, Equiv.swap_apply_right])
          (by rw [hli, Equiv.swap_apply_left]) _ _ c
      · have hjl : j ≠ l := fun h => hkl (hkj.trans h)
        have hil : i ≠ l := fun h => hli h.symm
        rw [x_congr hkj rfl hkl hjl c, weyl_conj_row_right h2 i j l hij hil hjl c]
        exact x_congr (by rw [hkj, Equiv.swap_apply_right])
          (Equiv.swap_apply_of_ne_of_ne hil.symm hjl.symm).symm _ _ c
    · by_cases hli : l = i
      · rw [x_congr rfl hli hkl hki c, weyl_conj_col_left h2 i j k hij hki hkj c]
        exact x_congr (Equiv.swap_apply_of_ne_of_ne hki hkj).symm
          (by rw [hli, Equiv.swap_apply_left]) _ _ c
      · by_cases hlj : l = j
        · rw [x_congr rfl hlj hkl hkj c, weyl_conj_col_right h2 i j k hij hki hkj c]
          exact x_congr (Equiv.swap_apply_of_ne_of_ne hki hkj).symm
            (by rw [hlj, Equiv.swap_apply_right]) _ _ c
        · rw [weyl_conj_disjoint i j k l hij hkl hki hkj hli hlj c]
          exact x_congr (Equiv.swap_apply_of_ne_of_ne hki hkj).symm
            (Equiv.swap_apply_of_ne_of_ne hli hlj).symm _ _ c

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_x_of_third

/-- **Lane sk-leavitt-01, `weyl_conj_x`.**  In `St_n(R)` with `3 ≤ n` and `2 = 0` in `R`,
`w_ij x_kl(c) w_ij⁻¹ = x_{σk, σl}(c)` with `σ = swap i j`. -/
theorem weyl_conj_x {n : ℕ} (h2 : (2 : R) = 0) (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (k l : Fin n) (hkl : k ≠ l) (c : R) :
    weyl i j hij * x k l hkl c * (weyl i j hij)⁻¹ =
      x (Equiv.swap i j k) (Equiv.swap i j l) ((Equiv.swap i j).injective.ne hkl) c :=
  weyl_conj_x_of_third h2 hij (WeylCalc.exists_third hn i j) k l hkl c

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_x

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
