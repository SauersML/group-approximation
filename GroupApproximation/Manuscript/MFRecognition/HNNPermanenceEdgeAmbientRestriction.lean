import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientMaps

/-! Corona conjugation restricted to the two ambient edge images. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem coronaConjugation_mem_target
    (data : CoronaConjugator G S T phi A X) (x : sourceAmbient data) :
    coronaConjugation data (x : Corona X) ∈ targetAmbient data := by
  let sx : sourceEdgeAlgebra data := (sourceAmbientMap data).symm x
  have hsx := forwardCoronaHom_mem data sx
  have hcoe : baseToCorona data (sx : baseAlgebra data) =
      (x : Corona X) := by
    exact starSubalgebraMapEquivOfInjective_symm_coe
      (sourceEdgeAlgebra data) (baseToCorona data)
      (baseToCorona_injective data) x
  change coronaConjugation data (x : Corona X) ∈ targetAmbient data
  rw [← hcoe]
  exact hsx

theorem coronaConjugation_symm_mem_source
    (data : CoronaConjugator G S T phi A X) (x : targetAmbient data) :
    (coronaConjugation data).symm (x : Corona X) ∈ sourceAmbient data := by
  let tx : targetEdgeAlgebra data := (targetAmbientMap data).symm x
  have htx := backwardCoronaHom_mem data tx
  have hcoe : baseToCorona data (tx : baseAlgebra data) =
      (x : Corona X) := by
    exact starSubalgebraMapEquivOfInjective_symm_coe
      (targetEdgeAlgebra data) (baseToCorona data)
      (baseToCorona_injective data) x
  change (coronaConjugation data).symm (x : Corona X) ∈ sourceAmbient data
  rw [← hcoe]
  exact htx

def ambientEdgeEquiv (data : CoronaConjugator G S T phi A X) :
    sourceAmbient data ≃⋆ₐ[ℂ] targetAmbient data :=
  restrictStarAlgEquivBetween (sourceAmbient data) (targetAmbient data)
    (coronaConjugation data) (coronaConjugation_mem_target data)
    (coronaConjugation_symm_mem_source data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
