import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCompatibility

/-! # The bundled carrier type for Ueda's full amalgam -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

/-- A C-star algebra bundled with its carrier, so downstream typeclass search
does not unfold the universe-sized universal product. -/
structure PackagedCStarAlgebra where
  carrier : Type 1
  [instCStarAlgebra : CStarAlgebra carrier]

instance : CoeSort PackagedCStarAlgebra (Type 1) :=
  ⟨PackagedCStarAlgebra.carrier⟩

noncomputable instance (P : PackagedCStarAlgebra) : CStarAlgebra P :=
  P.instCStarAlgebra

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
