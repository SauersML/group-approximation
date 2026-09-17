import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Commutator.Basic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Weyl.Conjugation

/-!
# Weyl conjugation of every root and the braid relation (glue for `K₂(4, L) = ⊥`)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  This is the Weyl calculus used in
the proof of Khanh (arXiv:2609.08428), Thm 5.1, for the edge and triangle relations of Brown's
presentation.

Assume `2 = 0` in `R`, let `σ = swap i j`, and suppose some index lies outside `{i, j}`.

* `weyl_conj_x_of_third`: `w_ij x_kl(c) w_ij⁻¹ = x_{σk, σl}(c)`.  The corner roots use
  `x_ij(c) = ⁅x_im(c), x_mj(1)⁆`; the other cases are the one-index cases of
  `LeavittK2.Weyl.Conjugation`.
* `weyl_conj_weyl_of_third`: `w_ij w_kl w_ij⁻¹ = w_{σk, σl}`.
* `weyl_braid`: `w_ij w_jk w_ij = w_jk w_ij w_jk` in `St_n(R)`, `3 ≤ n`.

This ports the unwired foreign drafts `LeavittK2/Weyl/{Corner,Braid}.lean`, whose history contains
a WIP snapshot.
-/

namespace GroupApproximation.Full.LVAssembly

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.WeylCalc

/-- In `Fin n` with `3 ≤ n`, any two indices leave a third one. -/
theorem exists_third_index {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
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

/-- **Weyl conjugation of a root.**  If `2 = 0` and some index lies outside `{i, j}`, then
`w_ij x_kl(c) w_ij⁻¹ = x_{σk, σl}(c)` with `σ = swap i j` (Khanh, Thm 5.1, Weyl calculus). -/
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

/-- `w_ij x_kl(c) w_ij⁻¹ = x_{σk, σl}(c)` in `St_n(R)` with `3 ≤ n` and `2 = 0`. -/
theorem weyl_conj_x {n : ℕ} (h2 : (2 : R) = 0) (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (k l : Fin n) (hkl : k ≠ l) (c : R) :
    weyl i j hij * x k l hkl c * (weyl i j hij)⁻¹ =
      x (Equiv.swap i j k) (Equiv.swap i j l) ((Equiv.swap i j).injective.ne hkl) c :=
  weyl_conj_x_of_third h2 hij (exists_third_index hn i j) k l hkl c

/-- `w_ij w_kl w_ij⁻¹ = w_{σk, σl}` with `σ = swap i j`, when `2 = 0` and a third index exists. -/
theorem weyl_conj_weyl_of_third (h2 : (2 : R) = 0) {i j : I} (hij : i ≠ j)
    (hthird : ∃ m : I, m ≠ i ∧ m ≠ j) (k l : I) (hkl : k ≠ l) :
    weyl (R := R) i j hij * weyl k l hkl * (weyl i j hij)⁻¹ =
      weyl (Equiv.swap i j k) (Equiv.swap i j l) ((Equiv.swap i j).injective.ne hkl) := by
  have e1 := weyl_conj_x_of_third h2 hij hthird k l hkl (1 : R)
  have e2 := weyl_conj_x_of_third h2 hij hthird l k hkl.symm (1 : R)
  calc weyl (R := R) i j hij * weyl k l hkl * (weyl i j hij)⁻¹
      = (weyl i j hij * x k l hkl (1 : R) * (weyl i j hij)⁻¹) *
          (weyl i j hij * x l k hkl.symm (1 : R) * (weyl i j hij)⁻¹) *
          (weyl i j hij * x k l hkl (1 : R) * (weyl i j hij)⁻¹) := by
        show weyl (R := R) i j hij *
            (x k l hkl (1 : R) * x l k hkl.symm (1 : R) * x k l hkl (1 : R)) *
            (weyl i j hij)⁻¹ = _
        group
    _ = weyl (Equiv.swap i j k) (Equiv.swap i j l) ((Equiv.swap i j).injective.ne hkl) := by
        rw [e1, e2, weyl]

/-- **Braid relation, general index type.**  If `2 = 0` and any two indices leave a third, then
`w_ij w_jk w_ij = w_jk w_ij w_jk` for distinct `i, j, k`. -/
theorem weyl_braid_of_third (h2 : (2 : R) = 0) (h3 : ∀ a b : I, ∃ m : I, m ≠ a ∧ m ≠ b)
    {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    weyl (R := R) i j hij * weyl j k hjk * weyl i j hij =
      weyl j k hjk * weyl i j hij * weyl j k hjk := by
  have e1 : weyl (R := R) i j hij * weyl j k hjk * (weyl i j hij)⁻¹ = weyl i k hik := by
    rw [weyl_conj_weyl_of_third h2 hij (h3 i j) j k hjk]
    exact weyl_congr (Equiv.swap_apply_right i j)
      (Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm) _ _
  have e2 : weyl (R := R) j k hjk * weyl i j hij * (weyl j k hjk)⁻¹ = weyl i k hik := by
    rw [weyl_conj_weyl_of_third h2 hjk (h3 j k) i j hij]
    exact weyl_congr (Equiv.swap_apply_of_ne_of_ne hij hik) (Equiv.swap_apply_left j k) _ _
  rw [weyl_inv h2] at e1 e2
  exact e1.trans e2.symm

/-- **Braid relation** in `St_n(R)`, `3 ≤ n`, `2 = 0`: `w_ij w_jk w_ij = w_jk w_ij w_jk`
(the triangle relation `ThT = hTh` of Khanh, Thm 5.1). -/
theorem weyl_braid {n : ℕ} (h2 : (2 : R) = 0) (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    weyl (R := R) i j hij * weyl j k hjk * weyl i j hij =
      weyl j k hjk * weyl i j hij * weyl j k hjk :=
  weyl_braid_of_third h2 (exists_third_index hn) hij hjk hik

end GroupApproximation.Full.LVAssembly
