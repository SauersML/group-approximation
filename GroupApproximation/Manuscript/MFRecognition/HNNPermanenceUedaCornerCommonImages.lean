import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitEleven

/-! # Common-image identities used by Ueda's corner covariance -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem amalgam_diagonal_source_zero_common
    (data : CoronaConjugator G S T phi A X) (b : sourceEdgeAlgebra data) :
    amalgamLeft data (cStarDiagonalTwo (b : baseAlgebra data) 0) =
      amalgamRight data (cStarDiagonalTwo b 0) := by
  have h := amalgam_commonImage data
    (b, (0 : targetEdgeAlgebra data))
  change amalgamLeft data
      (cStarDiagonalTwo (b : baseAlgebra data)
        ((0 : targetEdgeAlgebra data) : baseAlgebra data)) =
    amalgamRight data
      (cStarDiagonalTwo b
        ((edgeIsomorphism data).symm (0 : targetEdgeAlgebra data))) at h
  simpa only [ZeroMemClass.coe_zero, map_zero] using h

theorem amalgam_zero_diagonal_edge_common
    (data : CoronaConjugator G S T phi A X) (b : sourceEdgeAlgebra data) :
    amalgamRight data (cStarDiagonalTwo 0 b) =
      amalgamLeft data
        (cStarDiagonalTwo 0
          ((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data)) := by
  have h := amalgam_commonImage data
    ((0 : sourceEdgeAlgebra data), edgeIsomorphism data b)
  change amalgamLeft data
      (cStarDiagonalTwo
        ((0 : sourceEdgeAlgebra data) : baseAlgebra data)
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) =
    amalgamRight data
      (cStarDiagonalTwo (0 : sourceEdgeAlgebra data)
        ((edgeIsomorphism data).symm (edgeIsomorphism data b))) at h
  simpa only [ZeroMemClass.coe_zero, StarAlgEquiv.symm_apply_apply] using h.symm

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
