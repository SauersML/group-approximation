import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceConstructedEdgeDef

/-! Ambient conjugation formula for the constructed edge isomorphism. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem constructedEdgeIsomorphism_conj
    (data : CoronaConjugator G S T phi A X)
    (b : sourceEdgeAlgebra data) :
    coronaConjugation data
        (baseToCorona data (b : baseAlgebra data)) =
      baseToCorona data
        (((constructedEdgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) := by
  have hamb := restrictStarAlgEquivBetween_coe
    (sourceAmbient data) (targetAmbient data) (coronaConjugation data)
    (coronaConjugation_mem_target data)
    (coronaConjugation_symm_mem_source data) (sourceAmbientMap data b)
  have htarget := starSubalgebraMapEquivOfInjective_symm_coe
    (targetEdgeAlgebra data) (baseToCorona data)
    (baseToCorona_injective data)
    (ambientEdgeEquiv data (sourceAmbientMap data b))
  change coronaConjugation data
      (baseToCorona data (b : baseAlgebra data)) =
    baseToCorona data
      ((constructedEdgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data)
  exact hamb.trans htarget.symm

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
