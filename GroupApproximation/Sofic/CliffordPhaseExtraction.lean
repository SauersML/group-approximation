import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Quantitative extraction of the double-commutator Clifford phase

For involutive unitaries `C,D`, the matrix word corresponding to
`[C,[C,h]]` after writing `D=hCh⁻¹` is `D C D C`.  Its defect from the
central phase `-1` is exactly the anticommutator defect:

`||D C D C + 1||₂² = ||C D + D C||₂²`.

The proof is the algebraic factorization

`D (C D + D C) C = D C D C + 1`

and unitary invariance of normalized Hilbert--Schmidt norm.  Thus the
finite-matrix gate in `TRUE_KUN_THOM_CLIFFORD_PHASE.md` loses no constant
when it converts approximate anticommutation into the marked scalar phase.
-/

namespace GroupApproximation

open Matrix

/-- The matrix form of the second Clifford commutator. -/
def doubleCliffordWord {Y : Type*} [Fintype Y] [DecidableEq Y]
    (C D : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  D * C * D * C

/-- The double Clifford word plus one is a two-sided unitary transport of
the anticommutator. -/
theorem doubleCliffordWord_add_one_factorization
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (C D : Matrix Y Y ℂ) (hCsq : C * C = 1) (hDsq : D * D = 1) :
    doubleCliffordWord C D + 1 = D * (C * D + D * C) * C := by
  unfold doubleCliffordWord
  calc
    D * C * D * C + 1 = D * C * D * C + D * D * (C * C) := by
      rw [hCsq, Matrix.mul_one, hDsq]
    _ = D * (C * D + D * C) * C := by noncomm_ring

/-- **Exact quantitative phase extraction.**  For involutive unitaries, the
squared Hilbert--Schmidt defect of the double commutator from `-1` equals the
squared anticommutator defect. -/
theorem hsNormSq_doubleCliffordWord_add_one
    (Y : FiniteModel) {C D : Matrix Y Y ℂ}
    (hC : C ∈ Matrix.unitaryGroup Y ℂ)
    (hD : D ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y)
    (hCsq : C * C = 1) (hDsq : D * D = 1) :
    hsNormSq Y (doubleCliffordWord C D + 1) =
      hsNormSq Y (C * D + D * C) := by
  rw [doubleCliffordWord_add_one_factorization C D hCsq hDsq,
    hsNormSq_mul_right Y hC, hsNormSq_mul_left Y hD hY]

/-- Distance from the double Clifford word to the scalar `-1` is exactly the
anticommutator energy. -/
theorem hsDistSq_doubleCliffordWord_neg_one
    (Y : FiniteModel) {C D : Matrix Y Y ℂ}
    (hC : C ∈ Matrix.unitaryGroup Y ℂ)
    (hD : D ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y)
    (hCsq : C * C = 1) (hDsq : D * D = 1) :
    hsDistSq Y (doubleCliffordWord C D) (-1) =
      hsNormSq Y (C * D + D * C) := by
  change hsNormSq Y (doubleCliffordWord C D - (-1)) = _
  rw [sub_neg_eq_add,
    hsNormSq_doubleCliffordWord_add_one Y hC hD hY hCsq hDsq]

/-- A unitary within squared distance one of the scalar `-1` is uniformly
separated from the identity.  This is the coarse scalar-phase estimate used
to detect a nontrivial tracial-ultraproduct class. -/
theorem one_le_hsDistSq_one_of_negOneDefect_le_one
    (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (hdefect : hsDistSq Y U (-1) ≤ 1) :
    1 ≤ hsDistSq Y U 1 := by
  have hscalar : (-1 : Matrix Y Y ℂ) = (-1 : ℂ) • 1 := by simp
  change hsNormSq Y (U - (-1)) ≤ 1 at hdefect
  rw [hscalar, hsNormSq_sub_smul_one Y hU hY] at hdefect
  have hre : (normTrace Y U).re ≤ -1 / 2 := by
    norm_num at hdefect ⊢
    linarith
  have hone : (1 : Matrix Y Y ℂ) ∈ Matrix.unitaryGroup Y ℂ :=
    Submonoid.one_mem _
  rw [hsDistSq_of_unitary Y hU hone hY, Matrix.conjTranspose_one,
    Matrix.mul_one]
  linarith

/-- Exact anticommutation makes the double Clifford word the scalar `-1`. -/
theorem doubleCliffordWord_eq_neg_one_of_anticommute
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (C D : Matrix Y Y ℂ) (hCsq : C * C = 1)
    (hDsq : D * D = 1) (hanti : C * D + D * C = 0) :
    doubleCliffordWord C D = -1 := by
  have hfactor := doubleCliffordWord_add_one_factorization C D hCsq hDsq
  rw [hanti, Matrix.mul_zero, Matrix.zero_mul] at hfactor
  exact eq_neg_of_add_eq_zero_left hfactor

end GroupApproximation
