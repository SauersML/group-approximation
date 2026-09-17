import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.Defs
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.Core
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone: frames of `A^4` as units of `A`

Khanh (arXiv:2609.08428), Prop. `prop:selfsim` (used in the proof of `prop:frame-cone`):

> `Φ = L_r^* : R → R^r` is an isomorphism of right `R`-modules, and `GL_r(R) ≅ R^×`.

With the left-comb leaves `d_j`, `vecToScalar w = Σ_i d_i w_i` and
`scalarToVec x = (t_{w_i} x)_i` are mutually inverse (`vecToScalar_scalarToVec`,
`scalarToVec_vecToScalar`), and a list `f` of length `≤ 4` is a frame iff some unit `U` of `A`
has `U d_j = vecToScalar f_j` for `j < f.length` (`unit_of_frame`, `frame_of_unit`), through
`CompleteMatrixFamily.unitsEquiv`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone

open GroupApproximation

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- `Σ_i d_i w_i`. -/
def vecToScalar (w : Fin 4 → A) : A := ∑ i, L.wordS (leftCombWord 3 i) * w i

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.vecToScalar

/-- `(t_{w_i} x)_i`. -/
def scalarToVec (x : A) : Fin 4 → A := fun i => L.wordT (leftCombWord 3 i) * x

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.scalarToVec

theorem comb_orthogonal (i l : Fin 4) :
    L.wordT (leftCombWord 3 i) * L.wordS (leftCombWord 3 l) = if i = l then 1 else 0 :=
  L.prefixCode_orthogonal (leftCombCode 3) i l

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.comb_orthogonal

theorem comb_complete :
    ∑ i : Fin 4, L.wordS (leftCombWord 3 i) * L.wordT (leftCombWord 3 i) = 1 :=
  (combFamily L).complete

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.comb_complete

theorem vecToScalar_scalarToVec (x : A) : vecToScalar L (scalarToVec L x) = x := by
  unfold vecToScalar scalarToVec
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, comb_complete, one_mul]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.vecToScalar_scalarToVec

theorem right_mul_vecToScalar (w : Fin 4 → A) (i : Fin 4) :
    L.wordT (leftCombWord 3 i) * vecToScalar L w = w i := by
  unfold vecToScalar
  simp [Finset.mul_sum, ← mul_assoc, comb_orthogonal]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.right_mul_vecToScalar

theorem scalarToVec_vecToScalar (w : Fin 4 → A) : scalarToVec L (vecToScalar L w) = w :=
  funext fun i => right_mul_vecToScalar L w i

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.scalarToVec_vecToScalar

theorem comb_matrix_mul_left (M : Matrix (Fin 4) (Fin 4) A) (j : Fin 4) :
    (combFamily L).matrixRingEquiv M * L.wordS (leftCombWord 3 j) =
      ∑ i, L.wordS (leftCombWord 3 i) * M i j := by
  rw [CompleteMatrixFamily.matrixRingEquiv_apply]
  simp [combFamily_left, combFamily_right, Finset.sum_mul, mul_assoc, comb_orthogonal]

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.comb_matrix_mul_left

/-- A frame of `A^4` is carried by a unit of `A` on the comb leaves. -/
theorem unit_of_frame {f : List (Fin 4 → A)} (hf : IsFrame f) :
    ∃ U : Aˣ, ∀ (j : Fin 4) (hj : j.val < f.length),
      (U : A) * L.wordS (leftCombWord 3 j) = vecToScalar L (f[j.val]'hj) := by
  obtain ⟨-, g, hg⟩ := hf
  refine ⟨(combFamily L).unitsEquiv g, fun j hj => ?_⟩
  rw [CompleteMatrixFamily.unitsEquiv_apply_val, comb_matrix_mul_left]
  unfold vecToScalar
  exact Finset.sum_congr rfl fun i _ => by rw [hg j hj i]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.unit_of_frame

/-- Conversely, a unit of `A` carrying the comb leaves to a list gives a frame. -/
theorem frame_of_unit {f : List (Fin 4 → A)} (hlen : f.length ≤ 4) (U : Aˣ)
    (hU : ∀ (j : Fin 4) (hj : j.val < f.length),
      (U : A) * L.wordS (leftCombWord 3 j) = vecToScalar L (f[j.val]'hj)) :
    IsFrame f := by
  refine ⟨hlen, (combFamily L).unitsEquiv.symm U, fun j hj i => ?_⟩
  have hg : (((combFamily L).unitsEquiv.symm U : (Matrix (Fin 4) (Fin 4) A)ˣ) :
      Matrix (Fin 4) (Fin 4) A) = (combFamily L).matrixRingEquiv.symm (U : A) := by
    rw [RingEquiv.eq_symm_apply, ← CompleteMatrixFamily.unitsEquiv_apply_val,
      MulEquiv.apply_symm_apply]
  rw [hg, CompleteMatrixFamily.matrixRingEquiv_symm_apply, combFamily_right, combFamily_left,
    mul_assoc, hU j hj, right_mul_vecToScalar]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.frame_of_unit

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone
