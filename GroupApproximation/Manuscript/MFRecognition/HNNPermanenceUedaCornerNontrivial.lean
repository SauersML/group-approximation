import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerWord
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamInjective

/-! # Nontriviality of Ueda's corner -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

noncomputable instance cornerNontrivial
    (data : CoronaConjugator G S T phi A X) :
    Nontrivial (CStarCorner (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data)) := by
  refine ⟨1, 0, fun h ↦ ?_⟩
  have hcorner :
      amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data)) =
        amalgamLeft data 0 :=
    (congrArg Subtype.val h).trans (map_zero (amalgamLeft data)).symm
  have hmatrix : cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data) = 0 :=
    (amalgam_factorMaps_injective data).1 hcorner
  have hentry := congrArg
    (fun M : matrixBaseAlgebra data ↦ M 0 0) hmatrix
  simp [cStarMatrixUnitTwo] at hentry

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
