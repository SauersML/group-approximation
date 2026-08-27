import GroupApproximation.Analysis.ShulmanHalmosDilationDef

/-! Algebraic defect identities for the Halmos dilation. -/

namespace GroupApproximation
namespace ShulmanHalmosDilation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
noncomputable local instance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℂ (Mat₂ A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    ContinuousFunctionalCalculus ℝ (Mat₂ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance [Nontrivial A] :
    PartialOrder (Mat₂ A) := CStarAlgebra.spectralOrder (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    StarOrderedRing (Mat₂ A) := CStarAlgebra.spectralOrderedRing (Mat₂ A)

noncomputable local instance [Nontrivial A] :
    NonnegSpectrumClass ℝ (Mat₂ A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The square of the selfadjoint off-diagonal matrix is the diagonal of the
two Gram elements. -/
theorem selfAdjointOffDiag_sq (x : A) :
    selfAdjointOffDiag x * selfAdjointOffDiag x =
      diag₂ (x * star x) (star x * x) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointOffDiag, diag₂, CStarMatrix.mul_apply,
      Fin.sum_univ_two]

theorem selfAdjointOffDiag_isSelfAdjoint (x : A) :
    IsSelfAdjoint (selfAdjointOffDiag x) := by
  rw [IsSelfAdjoint]
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointOffDiag, CStarMatrix.star_eq_conjTranspose]

/-- The diagonal defect matrix is the positive square root of
`1 - selfAdjointOffDiag(x)^2`.  This matrix-level CFC argument supplies the
otherwise nontrivial pull-through identity between the two defect roots. -/
theorem sqrt_one_sub_selfAdjointOffDiag_sq [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    CFC.sqrt
        (1 - selfAdjointOffDiag x * selfAdjointOffDiag x) =
      diag₂ (leftDefect x) (rightDefect x) := by
  let T : Mat₂ A := selfAdjointOffDiag x
  let p : Mat₂ A := 1 - T * T
  let D : Mat₂ A := diag₂ (leftDefect x) (rightDefect x)
  have hpShape : p = diag₂ (1 - x * star x) (1 - star x * x) := by
    dsimp [p, T]
    rw [selfAdjointOffDiag_sq]
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diag₂]
  have hp : 0 ≤ p := by
    rw [hpShape]
    exact diag₂_nonneg (left_defect_argument_nonneg hx)
      (right_defect_argument_nonneg hx)
  have hD : 0 ≤ D := by
    exact diag₂_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _)
  have hDsquare : D * D = p := by
    rw [hpShape]
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [D, diag₂, leftDefect, rightDefect, CStarMatrix.mul_apply,
        Fin.sum_univ_two, CFC.sqrt_mul_sqrt_self,
        left_defect_argument_nonneg hx, right_defect_argument_nonneg hx]
  change CFC.sqrt p = D
  exact (CFC.sqrt_eq_iff p D hp hD).2 hDsquare

/-- The two defect square roots satisfy the Halmos pull-through identity. -/
theorem leftDefect_mul_eq_mul_rightDefect [Nontrivial A] {x : A} (hx : ‖x‖ ≤ 1) :
    leftDefect x * x = x * rightDefect x := by
  let T : Mat₂ A := selfAdjointOffDiag x
  let p : Mat₂ A := 1 - T * T
  let D : Mat₂ A := diag₂ (leftDefect x) (rightDefect x)
  have hpcomm : Commute p T := by
    rw [commute_iff_eq]
    dsimp [p]
    noncomm_ring
  have hsqrtcomm : Commute (CFC.sqrt p) T := by
    exact hpcomm.cfcₙ_nnreal NNReal.sqrt
  have hsqrt : CFC.sqrt p = D := by
    exact sqrt_one_sub_selfAdjointOffDiag_sq hx
  rw [hsqrt] at hsqrtcomm
  have hentry := congrArg (fun M : Mat₂ A => M 0 1) hsqrtcomm.eq
  simpa [D, T, diag₂, selfAdjointOffDiag, CStarMatrix.mul_apply,
    Fin.sum_univ_two] using hentry

/-- The adjoint pull-through identity. -/
theorem star_mul_leftDefect_eq_rightDefect_mul_star [Nontrivial A]
    {x : A} (hx : ‖x‖ ≤ 1) :
    star x * leftDefect x = rightDefect x * star x := by
  have h := congrArg star (leftDefect_mul_eq_mul_rightDefect hx)
  have hleftStar : star (leftDefect x) = leftDefect x :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  have hrightStar : star (rightDefect x) = rightDefect x :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
  rw [star_mul, star_mul, hleftStar, hrightStar] at h
  exact h

theorem leftDefect_mul_self {x : A} (hx : ‖x‖ ≤ 1) :
    leftDefect x * leftDefect x = 1 - x * star x := by
  exact CFC.sqrt_mul_sqrt_self _ (left_defect_argument_nonneg hx)

theorem rightDefect_mul_self {x : A} (hx : ‖x‖ ≤ 1) :
    rightDefect x * rightDefect x = 1 - star x * x := by
  exact CFC.sqrt_mul_sqrt_self _ (right_defect_argument_nonneg hx)

theorem star_leftDefect {x : A} : star (leftDefect x) = leftDefect x :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq

theorem star_rightDefect {x : A} : star (rightDefect x) = rightDefect x :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq

end

end ShulmanHalmosDilation
end GroupApproximation
