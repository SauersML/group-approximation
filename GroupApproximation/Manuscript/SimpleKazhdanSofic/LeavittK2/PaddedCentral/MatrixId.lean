import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import GroupApproximation.Meta.AxiomGuard

/-!
# Elementary matrices acting on basis vectors (lane sk-leavitt-03, matrix side)

Carto `sk-leavitt` lane 03 (Khanh Lemma 5.6), matrix bookkeeping over an arbitrary ring `R`.
For `E = 1 + e_{ij}(b)`:

* `E *ᵥ e_j(a) = e_j(a) + e_i(b a)`, and `E *ᵥ e_p(a) = e_p(a)` when `p ≠ j`;
* `e_i(a) ᵥ* E = e_i(a) + e_j(a b)`, and `e_p(a) ᵥ* E = e_p(a)` when `p ≠ i`.

Here `e_p(a) = Pi.single p a`. These are the matrix shadows of the Steinberg conjugation
formulas in `PaddedCentral.Conj`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

open scoped Matrix

variable {R : Type*} [Ring R] {n : ℕ}

/-- `e_{ij}(b) *ᵥ w = e_i(b · w j)`. -/
theorem single_mulVec_eq_pi (i j : Fin n) (b : R) (w : Fin n → R) :
    Matrix.single i j b *ᵥ w = Pi.single i (b * w j) :=
  Matrix.single_mulVec i j b w

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.single_mulVec_eq_pi

theorem one_add_single_mulVec_single_same (i j : Fin n) (b a : R) :
    (1 + Matrix.single i j b) *ᵥ Pi.single j a = Pi.single j a + Pi.single i (b * a) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq_pi, Pi.single_eq_same]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.one_add_single_mulVec_single_same

theorem one_add_single_mulVec_single_of_ne {i j p : Fin n} (hp : p ≠ j) (b a : R) :
    (1 + Matrix.single i j b) *ᵥ Pi.single p a = Pi.single p a := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq_pi, Pi.single_eq_of_ne' hp a,
    mul_zero, Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.one_add_single_mulVec_single_of_ne

/-- Entries of `e_p(a) ᵥ* M`. -/
theorem single_vecMul_apply (p : Fin n) (a : R) (M : Matrix (Fin n) (Fin n) R) (q : Fin n) :
    (Pi.single p a ᵥ* M) q = a * M p q :=
  congrFun (Matrix.single_vecMul M p a) q

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.single_vecMul_apply

theorem single_vecMul_single_same (i j : Fin n) (a b : R) :
    Pi.single i a ᵥ* Matrix.single i j b = Pi.single j (a * b) := by
  funext q
  rw [single_vecMul_apply]
  by_cases hq : q = j
  · rw [hq, Matrix.single_apply_same, Pi.single_eq_same]
  · rw [Matrix.single_apply_of_col_ne i i (Ne.symm hq) b, mul_zero, Pi.single_eq_of_ne hq]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.single_vecMul_single_same

theorem single_vecMul_single_of_ne {i j p : Fin n} (hp : p ≠ i) (a b : R) :
    Pi.single p a ᵥ* Matrix.single i j b = 0 := by
  funext q
  rw [single_vecMul_apply, Matrix.single_apply_of_row_ne (Ne.symm hp) j q b, mul_zero,
    Pi.zero_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.single_vecMul_single_of_ne

theorem single_vecMul_one_add_single_same (i j : Fin n) (a b : R) :
    Pi.single i a ᵥ* (1 + Matrix.single i j b) = Pi.single i a + Pi.single j (a * b) := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one, single_vecMul_single_same]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.single_vecMul_one_add_single_same

theorem single_vecMul_one_add_single_of_ne {i j p : Fin n} (hp : p ≠ i) (a b : R) :
    Pi.single p a ᵥ* (1 + Matrix.single i j b) = Pi.single p a := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one, single_vecMul_single_of_ne hp, add_zero]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.single_vecMul_one_add_single_of_ne

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
