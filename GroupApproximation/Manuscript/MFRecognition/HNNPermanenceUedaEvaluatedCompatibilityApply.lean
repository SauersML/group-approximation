import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedCovariance

/-! # Pointwise compatibility of the evaluated Ueda factor maps -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

theorem evaluatedFactor_compatible_apply (R : HNNCoordinate data)
    (c : edgeSumAlgebra data) :
    evaluatedFactorRight data R (amalgamRightInclusion data c) =
      evaluatedFactorLeft data R (amalgamLeftInclusion data c) := by
  have hconj := evaluated_covariance_conj data R
    ((edgeIsomorphism data).symm c.2)
  rw [StarAlgEquiv.apply_symm_apply] at hconj
  have hright : evaluatedFactorRight data R (amalgamRightInclusion data c) =
      cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier) *
          matrixTwoMap R.base
            (matrixEdgeInclusion data (amalgamRightInclusion data c)) *
        star (cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier)) :=
    rfl
  have hleft : evaluatedFactorLeft data R (amalgamLeftInclusion data c) =
      matrixTwoMap R.base (amalgamLeftInclusion data c) :=
    rfl
  have hincl : matrixEdgeInclusion data
        (cStarDiagonalTwo c.1 ((edgeIsomorphism data).symm c.2)) =
      cStarDiagonalTwo ((c.1 : baseAlgebra data))
        ((((edgeIsomorphism data).symm c.2 : sourceEdgeAlgebra data) :
          baseAlgebra data)) :=
    matrixTwoMap_diagonal _ _ _
  rw [hright, hleft, amalgamRightInclusion_apply, amalgamLeftInclusion_apply,
    hincl]
  simp only [matrixTwoMap_diagonal]
  rw [conj_cStarDiagonalTwo, star_one, one_mul, mul_one, hconj]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
