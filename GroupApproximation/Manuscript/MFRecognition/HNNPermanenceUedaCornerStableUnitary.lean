import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerWord

/-! # The canonical corner unitary in Ueda's model -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

def cornerStableUnitary (data : CoronaConjugator G S T phi A X) :
    unitary (CStarCorner (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data)) :=
  (exists_cornerWord_unitary data).choose

@[simp] theorem coe_cornerStableUnitary
    (data : CoronaConjugator G S T phi A X) :
    (((cornerStableUnitary data :
        unitary (CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data))) :
      CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data)) : amalgam data) =
      matrixUnitLeft data 0 1 * matrixUnitRight data 1 0 :=
  (exists_cornerWord_unitary data).choose_spec

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
