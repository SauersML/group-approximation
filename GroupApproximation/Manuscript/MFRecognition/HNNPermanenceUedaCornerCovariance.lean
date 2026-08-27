import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBaseCornerMap
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerCovarianceAmbient
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerStableUnitary

/-! # Covariance of the canonical base map and Ueda corner unitary -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem cornerStableUnitary_covariance_conj
    (data : CoronaConjugator G S T phi A X) (b : sourceEdgeAlgebra data) :
    (cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) *
        cornerBaseMap data (b : baseAlgebra data) *
      star (cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) =
    cornerBaseMap data
      ((edgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data) := by
  apply Subtype.ext
  -- `cornerStableUnitary` is a chosen witness, so its value in the amalgam is
  -- a theorem (`coe_cornerStableUnitary`), not a reduction; a `change` onto
  -- the corner word can never hold definitionally.  The subtype operations do
  -- distribute definitionally, so `show` gets us to a goal the rewrite fits.
  show ((cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) : amalgam data) *
      ((cornerBaseMap data (b : baseAlgebra data) :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) : amalgam data) *
      star ((cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) : amalgam data) =
    ((cornerBaseMap data
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data) :
      CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data)) : amalgam data)
  rw [coe_cornerStableUnitary]
  exact cornerWord_covariance_ambient data b

theorem cornerStableUnitary_covariance
    (data : CoronaConjugator G S T phi A X) (b : sourceEdgeAlgebra data) :
    (cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) *
        cornerBaseMap data (b : baseAlgebra data) =
      cornerBaseMap data
          ((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data) *
        (cornerStableUnitary data :
          CStarCorner (cornerUnit data) (cornerUnit_star data)
            (cornerUnit_mul data)) := by
  calc
    (cornerStableUnitary data :
          CStarCorner (cornerUnit data) (cornerUnit_star data)
            (cornerUnit_mul data)) *
        cornerBaseMap data (b : baseAlgebra data) =
      ((cornerStableUnitary data :
            CStarCorner (cornerUnit data) (cornerUnit_star data)
              (cornerUnit_mul data)) *
          cornerBaseMap data (b : baseAlgebra data) *
        star (cornerStableUnitary data :
          CStarCorner (cornerUnit data) (cornerUnit_star data)
            (cornerUnit_mul data))) *
          (cornerStableUnitary data :
            CStarCorner (cornerUnit data) (cornerUnit_star data)
              (cornerUnit_mul data)) := by
        rw [mul_assoc, (cornerStableUnitary data).property.1, mul_one]
    _ = cornerBaseMap data
          ((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data) *
        (cornerStableUnitary data :
          CStarCorner (cornerUnit data) (cornerUnit_star data)
            (cornerUnit_mul data)) := by
      rw [cornerStableUnitary_covariance_conj]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
