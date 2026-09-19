import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaUniversalMapDef

/-! # Generator formulas for the universal HNN map into Ueda's corner -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

@[simp] theorem uedaCornerMap_base (hUeda : UedaCornerMapStatement)
    (data : CoronaConjugator G S T phi A X) (d : baseAlgebra data) :
    uedaCornerMap hUeda data (universalBase data d) = cornerBaseMap data d :=
  (hUeda data).choose_spec.1 d

@[simp] theorem uedaCornerMap_stable (hUeda : UedaCornerMapStatement)
    (data : CoronaConjugator G S T phi A X) :
    uedaCornerMap hUeda data
        ((universalStable data : unitary (universalHNN data)) :
          universalHNN data) =
      (cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) :=
  (hUeda data).choose_spec.2.1

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
