import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Weyl.Corner
import GroupApproximation.Meta.AxiomGuard

/-!
# The braid relation for Weyl elements (lane sk-leavitt-01)

Assume `2 = 0` in `R` and that any two indices leave a third (in `Fin n`: `3 ≤ n`).

* Conjugating a Weyl element (`weyl_conj_weyl_of_third`).  `w_kl = x_kl(1) x_lk(1) x_kl(1)`, so
  conjugating by `w_ij` factor by factor with `weyl_conj_x_of_third` gives
  `w_ij w_kl w_ij⁻¹ = w_{σk, σl}` with `σ = swap i j`.
* Braid relation.  For distinct `i, j, k`, `w_ij w_jk w_ij⁻¹ = w_ik`, since `swap i j` maps
  `(j, k)` to `(i, k)`.  Likewise `w_jk w_ij w_jk⁻¹ = w_ik`, since `swap j k` maps `(i, j)` to
  `(i, k)`.  Both Weyl elements are involutions (`weyl_inv`), so
  `w_ij w_jk w_ij = w_ik = w_jk w_ij w_jk`.

Endpoints: `weyl_braid` (any distinct `i, j, k` in `Fin n`, `3 ≤ n`) and
`weyl_braid_zero_one_two`, which is the lane statement with indices `0, 1, 2`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup
open WeylCalc

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

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

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_weyl_of_third

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

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_braid_of_third

/-- **Lane sk-leavitt-01, `weyl_braid`.**  In `St_n(R)` with `3 ≤ n` and `2 = 0` in `R`,
`w_ij w_jk w_ij = w_jk w_ij w_jk` for distinct `i, j, k`. -/
theorem weyl_braid {n : ℕ} (h2 : (2 : R) = 0) (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    weyl (R := R) i j hij * weyl j k hjk * weyl i j hij =
      weyl j k hjk * weyl i j hij * weyl j k hjk :=
  weyl_braid_of_third h2 (WeylCalc.exists_third hn) hij hjk hik

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_braid

/-- The lane statement at the indices `0, 1, 2` of `Fin n`, `3 ≤ n`:
`w_01 w_12 w_01 = w_12 w_01 w_12`. -/
theorem weyl_braid_zero_one_two {n : ℕ} (h2 : (2 : R) = 0) (hn : 3 ≤ n) :
    weyl (R := R) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp) *
        weyl (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ (by simp) *
        weyl (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp) =
      weyl (R := R) (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ (by simp) *
        weyl (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp) *
        weyl (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩ (by simp) :=
  weyl_braid h2 hn _ _ (by simp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_braid_zero_one_two

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
