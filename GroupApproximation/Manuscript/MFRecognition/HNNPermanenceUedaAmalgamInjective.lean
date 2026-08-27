import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamRight

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNAmalgamCornerSentences

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Printed: *"in which `A₁` and `A₂` embed [Shulman, Section 2.1]"*.  In the
repository's construction of the full amalgam this is not a literature input:
it follows from the single compatible pair `(φ_A, φ_B)`, both of whose members
are injective. -/
theorem amalgam_factorMaps_injective
    (data : CoronaConjugator G S T phi A X) :
    Function.Injective (amalgamLeft data) ∧
      Function.Injective (amalgamRight data) :=
  manuscriptSentence_ce5f1d31a90e_factorMapsInjective
      (C := edgeSumAlgebra data) (A := matrixBaseAlgebra data)
      (B := matrixEdgeAlgebra data)
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    (coronaAmalgamRepresentation data) (coronaFactorLeft_injective data)
    (coronaFactorRight_injective data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
