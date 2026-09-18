import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStabGenSupport
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabFactorPar
import GroupApproximation.Meta.AxiomGuard

/-!
# Matrices of the root subgroup avoiding `c` fix `e_c` (lane bh-met-90l)

This holds over an arbitrary unital ring `R`.  Say `M` *fixes* `c` (`czTriOff_Fix c M`) when
`M e_c = e_c` and `e_c M = e_c`, i.e. the `c`-th column and the `c`-th row of `M` are those
of the identity.  Every root `x_{p,q}(a)` with `p ≠ c` and `q ≠ c` has a matrix fixing `c`,
so every element of `czStabGen_off R c` does (`czTriOff_fix_of_mem`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {N : ℕ}

/-- `M` fixes the basis vector `e_c` on both sides. -/
def czTriOff_Fix (c : Fin N) (M : Matrix (Fin N) (Fin N) R) : Prop :=
  M *ᵥ Pi.single c 1 = Pi.single c 1 ∧ Pi.single c 1 ᵥ* M = Pi.single c 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_Fix

/-- Generator case: a root avoiding `c` fixes `c`. -/
theorem czTriOff_fix_x {c p q : Fin N} (hpq : p ≠ q) (hp : p ≠ c) (hq : q ≠ c) (a : R) :
    czTriOff_Fix c (padMat (x p q hpq a)) := by
  rw [padMat_x]
  exact ⟨one_add_single_mulVec_single_of_ne hq.symm a 1,
    single_vecMul_one_add_single_of_ne hp.symm 1 a⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_fix_x

/-- Every element of the root subgroup avoiding `c` has a matrix fixing `c`. -/
theorem czTriOff_fix_of_mem {c : Fin N} {g : St N R} (hg : g ∈ czStabGen_off R c) :
    czTriOff_Fix c (padMat g) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨p, q, hpq, a, hp, hq, rfl⟩ := hg
    exact czTriOff_fix_x hpq hp hq a
  | one => exact ⟨by rw [map_one, Matrix.one_mulVec], by rw [map_one, Matrix.vecMul_one]⟩
  | mul g h _ _ ihg ihh =>
    refine ⟨?_, ?_⟩
    · rw [map_mul padMat g h, ← Matrix.mulVec_mulVec, ihh.1, ihg.1]
    · rw [map_mul padMat g h, ← Matrix.vecMul_vecMul, ihg.2, ihh.2]
  | inv g _ ih =>
    refine ⟨?_, ?_⟩
    · calc padMat g⁻¹ *ᵥ Pi.single c 1 = padMat g⁻¹ *ᵥ (padMat g *ᵥ Pi.single c 1) := by
            rw [ih.1]
        _ = Pi.single c 1 := by
            rw [Matrix.mulVec_mulVec, ← map_mul padMat g⁻¹ g, inv_mul_cancel, map_one,
              Matrix.one_mulVec]
    · calc Pi.single c 1 ᵥ* padMat g⁻¹ = Pi.single c 1 ᵥ* padMat g ᵥ* padMat g⁻¹ := by
            rw [ih.2]
        _ = Pi.single c 1 := by
            rw [Matrix.vecMul_vecMul, ← map_mul padMat g g⁻¹, mul_inv_cancel, map_one,
              Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_fix_of_mem

/-- A matrix fixing `c` has the `c`-th column of the identity. -/
theorem czTriOff_fix_col {c : Fin N} {M : Matrix (Fin N) (Fin N) R} (h : czTriOff_Fix c M)
    (a : Fin N) : M a c = (1 : Matrix (Fin N) (Fin N) R) a c := by
  have e := congrFun h.1 a
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at e
  rw [e]
  by_cases hac : a = c
  · rw [hac, Pi.single_eq_same, Matrix.one_apply_eq]
  · rw [Pi.single_eq_of_ne hac, Matrix.one_apply_ne hac]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_fix_col

/-- A matrix fixing `c` has the `c`-th row of the identity. -/
theorem czTriOff_fix_row {c : Fin N} {M : Matrix (Fin N) (Fin N) R} (h : czTriOff_Fix c M)
    (b : Fin N) : M c b = (1 : Matrix (Fin N) (Fin N) R) c b := by
  have e := congrFun h.2 b
  rw [Matrix.single_one_vecMul, Matrix.row_apply] at e
  rw [e]
  by_cases hbc : b = c
  · rw [hbc, Pi.single_eq_same, Matrix.one_apply_eq]
  · rw [Pi.single_eq_of_ne hbc, Matrix.one_apply_ne (Ne.symm hbc)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_fix_row

/-- `M e_c = e_c` gives `e_d ⬝ (M e_c) = e_d c`, used for the vanishing of coordinates. -/
theorem czTriOff_fix_mulVec_apply {c : Fin N} {M : Matrix (Fin N) (Fin N) R}
    (h : czTriOff_Fix c M) (v : Fin N → R) : v ᵥ* M ⬝ᵥ Pi.single c 1 = v c := by
  rw [← Matrix.dotProduct_mulVec, h.1, dotProduct_single, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_fix_mulVec_apply

/-- `e_c M = e_c` gives `(e_c M) ⬝ v = v c`. -/
theorem czTriOff_fix_vecMul_apply {c : Fin N} {M : Matrix (Fin N) (Fin N) R}
    (h : czTriOff_Fix c M) (v : Fin N → R) : Pi.single c 1 ⬝ᵥ M *ᵥ v = v c := by
  rw [Matrix.dotProduct_mulVec, h.2, single_dotProduct, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_fix_vecMul_apply

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
