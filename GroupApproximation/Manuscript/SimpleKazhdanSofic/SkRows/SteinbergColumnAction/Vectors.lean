import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.Generators
import Mathlib.Algebra.BigOperators.Pi
import GroupApproximation.Meta.AxiomGuard

/-!
# Elementary matrices on basis vectors, and reduction to basis vectors

Lane `sk-rows-13`.  No single tex sentence is formalized here.

* `col_vec_same`, `col_vec_other`: `(1 + c e_{pq}) e_q a = e_p (c a) + e_q a` and
  `(1 + c e_{pq}) e_i a = e_i a` for `i ≠ q`.
* `row_vec_same`, `row_vec_other`: `a e_p (1 + d e_{pq}) = e_p a + e_q (a d)` and
  `a e_i (1 + d e_{pq}) = e_i a` for `i ≠ p`.
* `conj_colProd_of_single`, `conj_rowProd_of_single`: if conjugation by `g` acts through a matrix on
  the single boundary roots, then it acts through that matrix on every vector product.  The proof
  writes `v = ∑_k e_k (v k)` (`Finset.univ_sum_single`) and uses additivity of `colProd`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality
open scoped Matrix

variable {m : ℕ} {R : Type*} [Ring R]

theorem col_vec_same (p q : Fin m) (hpq : p ≠ q) (c a : R) :
    (1 + Matrix.single p q c) *ᵥ Pi.single q a = Pi.single p (c * a) + Pi.single q a := by
  funext k
  rw [mulVec_single_apply, Pi.add_apply, Matrix.add_apply]
  by_cases hkp : k = p
  · rw [hkp, Matrix.one_apply_ne hpq, Matrix.single_apply_same, Pi.single_eq_same,
      Pi.single_eq_of_ne hpq, zero_add, add_zero]
  · rw [Pi.single_eq_of_ne hkp, Matrix.single_apply_of_row_ne (Ne.symm hkp), add_zero, zero_add]
    by_cases hkq : k = q
    · rw [hkq, Matrix.one_apply_eq, Pi.single_eq_same, one_mul]
    · rw [Matrix.one_apply_ne hkq, Pi.single_eq_of_ne hkq, zero_mul]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.col_vec_same

theorem col_vec_other (p q : Fin m) (c : R) {i : Fin m} (hiq : i ≠ q) (a : R) :
    (1 + Matrix.single p q c) *ᵥ Pi.single i a = Pi.single i a := by
  funext k
  rw [mulVec_single_apply, Matrix.add_apply, Matrix.single_apply_of_col_ne _ _ (Ne.symm hiq),
    add_zero]
  by_cases hki : k = i
  · rw [hki, Matrix.one_apply_eq, Pi.single_eq_same, one_mul]
  · rw [Matrix.one_apply_ne hki, Pi.single_eq_of_ne hki, zero_mul]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.col_vec_other

theorem row_vec_same (p q : Fin m) (hpq : p ≠ q) (d a : R) :
    Pi.single p a ᵥ* (1 + Matrix.single p q d) = Pi.single p a + Pi.single q (a * d) := by
  funext k
  rw [vecMul_single_apply, Pi.add_apply, Matrix.add_apply, mul_add]
  by_cases hkq : k = q
  · rw [hkq, Matrix.one_apply_ne hpq, Matrix.single_apply_same, Pi.single_eq_same,
      Pi.single_eq_of_ne hpq.symm, mul_zero, zero_add]
  · rw [Pi.single_eq_of_ne hkq, Matrix.single_apply_of_col_ne _ _ (Ne.symm hkq), mul_zero,
      add_zero]
    by_cases hkp : k = p
    · rw [hkp, Matrix.one_apply_eq, Pi.single_eq_same, mul_one]
    · rw [Matrix.one_apply_ne (Ne.symm hkp), Pi.single_eq_of_ne hkp, mul_zero]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.row_vec_same

theorem row_vec_other (p q : Fin m) (d : R) {i : Fin m} (hip : i ≠ p) (a : R) :
    Pi.single i a ᵥ* (1 + Matrix.single p q d) = Pi.single i a := by
  funext k
  rw [vecMul_single_apply, Matrix.add_apply, Matrix.single_apply_of_row_ne (Ne.symm hip),
    add_zero]
  by_cases hki : k = i
  · rw [hki, Matrix.one_apply_eq, Pi.single_eq_same, mul_one]
  · rw [Matrix.one_apply_ne (Ne.symm hki), Pi.single_eq_of_ne hki, mul_zero]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.row_vec_other

theorem conj_mul_conj {G : Type*} [Group G] (g a b : G) :
    g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.conj_mul_conj

theorem conj_colProd_of_single (g : St (m + 1) R) (M : Matrix (Fin m) (Fin m) R)
    (h : ∀ (i : Fin m) (a : R), g * colRoot m R i a * g⁻¹ = colProd (M *ᵥ Pi.single i a))
    (v : Fin m → R) : g * colProd v * g⁻¹ = colProd (M *ᵥ v) := by
  have hs : ∀ s : Finset (Fin m), g * colProd (∑ k ∈ s, Pi.single k (v k)) * g⁻¹ =
      colProd (M *ᵥ ∑ k ∈ s, Pi.single k (v k)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, colProd_zero, Matrix.mulVec_zero, colProd_zero, mul_one,
        mul_inv_cancel]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, colProd_add, Matrix.mulVec_add, colProd_add, ← ih, ← h,
        colProd_single, conj_mul_conj]
  have hv := hs Finset.univ
  rw [Finset.univ_sum_single] at hv
  exact hv

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.conj_colProd_of_single

theorem conj_rowProd_of_single (g : St (m + 1) R) (M : Matrix (Fin m) (Fin m) R)
    (h : ∀ (i : Fin m) (a : R), g * rowRoot m R i a * g⁻¹ = rowProd (Pi.single i a ᵥ* M))
    (v : Fin m → R) : g * rowProd v * g⁻¹ = rowProd (v ᵥ* M) := by
  have hs : ∀ s : Finset (Fin m), g * rowProd (∑ k ∈ s, Pi.single k (v k)) * g⁻¹ =
      rowProd ((∑ k ∈ s, Pi.single k (v k)) ᵥ* M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, rowProd_zero, Matrix.zero_vecMul, rowProd_zero, mul_one,
        mul_inv_cancel]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, rowProd_add, Matrix.add_vecMul, rowProd_add, ← ih, ← h,
        rowProd_single, conj_mul_conj]
  have hv := hs Finset.univ
  rw [Finset.univ_sum_single] at hv
  exact hv

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.conj_rowProd_of_single

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction
