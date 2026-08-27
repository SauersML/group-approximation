import GroupApproximation.Analysis.UniversalCStarHNN
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeCovariance

/-! The corona covariant representation of the universal HNN object. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## The universal `C*`-HNN algebra `U` -/

/-- The printed covariant pair `(ι, W)` in the corona, as a member of the
representation family defining `U`. -/
def coronaCovariantRepresentation (data : CoronaConjugator G S T phi A X) :
    CStarHNNRepresentation (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
      (edgeIsomorphism data) :=
  CStarHNNRepresentation.ofCovariantPair (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data)
    (baseAlgebra data).subtype data.W (edgeIsomorphism_covariance data)

instance nonempty_coronaCovariantRepresentation
    (data : CoronaConjugator G S T phi A X) :
    Nonempty (CStarHNNRepresentation (sourceEdgeAlgebra data)
      (targetEdgeAlgebra data) (edgeIsomorphism data)) :=
  ⟨coronaCovariantRepresentation data⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
