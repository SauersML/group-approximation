import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamInjective

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNAmalgamCornerSentences

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The two canonical maps agree on `C`. -/
theorem amalgam_commonImage (data : CoronaConjugator G S T phi A X)
    (c : edgeSumAlgebra data) :
    amalgamLeft data (amalgamLeftInclusion data c) =
      amalgamRight data (amalgamRightInclusion data c) :=
  manuscriptSentence_68cf3b4da8ab_commonImage
      (C := edgeSumAlgebra data) (A := matrixBaseAlgebra data)
      (B := matrixEdgeAlgebra data)
    (amalgamLeftInclusion data) (amalgamRightInclusion data) c

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
