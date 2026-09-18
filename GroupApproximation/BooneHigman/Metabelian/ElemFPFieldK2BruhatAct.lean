import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoInjective
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal
import GroupApproximation.Meta.AxiomGuard

/-!
# Diagonal Steinberg elements acting on column vectors

Lane `bh-met-55`.  Two small facts about the diagonal element `h_ij(c) = w_ij(c) w_ij(-1)`
of `St_I(R)`, used by the faithfulness induction of `ElemFPFieldK2BruhatStatement`.

* `bruhat_h_one`: `h_ij(1) = 1`.  This follows from `w_ij(1)⁻¹ = w_ij(-1)` (`w_inv`).
* `bruhat_act_h_unitVec`: `h_ij(c) e_j = c⁻¹ e_j`, coordinate by coordinate.  The projection of
  `h_ij(c)` is `diag(c at i, c⁻¹ at j, 1 elsewhere)`
  (`manuscriptSentence_projectionDiagonalElement`), and `diagonal d *ᵥ e_j = d j • e_j`.

`act` and `unitVec` are the vector action and basis vectors of the `FieldTwo` corpus
(`LeavittK2/FieldTwoAction`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h w_inv
  manuscriptSentence_projectionDiagonalElement)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec
  unitVec_apply)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- `h_ij(1) = 1`. -/
theorem bruhat_h_one (i j : I) (hij : i ≠ j) : h (R := R) i j hij 1 = 1 := by
  rw [h, ← w_inv, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhat_h_one

/-- `h_ij(c) e_j = c⁻¹ e_j`, coordinate by coordinate. -/
theorem bruhat_act_h_unitVec (i j : I) (hij : i ≠ j) (c : Rˣ) (k : I) :
    act (h i j hij c) (unitVec j) k = if k = j then ((c⁻¹ : Rˣ) : R) else 0 := by
  simp only [act]
  rw [manuscriptSentence_projectionDiagonalElement, Matrix.mulVec_diagonal, unitVec_apply]
  by_cases hk : k = j
  · have hki : ¬(k = i) := fun e => hij (e.symm.trans hk)
    simp only [if_neg hki, if_pos hk, mul_one]
  · simp only [if_neg hk, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhat_act_h_unitVec

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
