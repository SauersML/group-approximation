import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientDef

/-! Closedness and generator transport for the ambient edge algebras. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem targetAmbient_isClosed (data : CoronaConjugator G S T phi A X) :
    IsClosed (targetAmbient data : Set (Corona X)) := by
  rw [targetAmbient, StarSubalgebra.coe_map]
  exact (baseAlgebra_isClosed data).isClosedMap_subtype_val _
    (targetEdgeAlgebra_isClosed data)

theorem sourceAmbient_isClosed (data : CoronaConjugator G S T phi A X) :
    IsClosed (sourceAmbient data : Set (Corona X)) := by
  rw [sourceAmbient, StarSubalgebra.coe_map]
  exact (baseAlgebra_isClosed data).isClosedMap_subtype_val _
    (sourceEdgeAlgebra_isClosed data)

theorem forwardCoronaHom_generator
    (data : CoronaConjugator G S T phi A X) (s : S) :
    forwardCoronaHom data
        (((baseUnitaryHom data).comp S.subtype s :
          unitary (baseAlgebra data)) : baseAlgebra data) ∈
      targetAmbient data := by
  let t : targetEdgeAlgebra data :=
    ((targetGenerator data s : unitary (targetEdgeAlgebra data)) :
      targetEdgeAlgebra data)
  refine ⟨(t : baseAlgebra data), t.property, ?_⟩
  change data.iota
        ((data.realization.rho ((phi s : T) : G) : unitary A) : A) =
    (data.W : Corona X) *
        data.iota ((data.realization.rho (s : G) : unitary A) : A) *
      star (data.W : Corona X)
  exact (data.conjugates s).symm

theorem backwardCoronaHom_generator
    (data : CoronaConjugator G S T phi A X) (s : S) :
    backwardCoronaHom data
        (((baseUnitaryHom data).comp (edgeHom phi) s :
          unitary (baseAlgebra data)) : baseAlgebra data) ∈
      sourceAmbient data := by
  let r : sourceEdgeAlgebra data :=
    ((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
      sourceEdgeAlgebra data)
  refine ⟨(r : baseAlgebra data), r.property, ?_⟩
  have hF : coronaConjugation data (baseToCorona data (r : baseAlgebra data)) =
      baseToCorona data
        ((((targetGenerator data s : unitary (targetEdgeAlgebra data)) :
          targetEdgeAlgebra data) : baseAlgebra data)) := by
    change (data.W : Corona X) *
        data.iota ((data.realization.rho (s : G) : unitary A) : A) *
          star (data.W : Corona X) =
      data.iota
        ((data.realization.rho ((phi s : T) : G) : unitary A) : A)
    exact data.conjugates s
  have h := congrArg (coronaConjugation data).symm hF
  have h' : baseToCorona data (r : baseAlgebra data) =
      (coronaConjugation data).symm
        (baseToCorona data
          ((((targetGenerator data s : unitary (targetEdgeAlgebra data)) :
            targetEdgeAlgebra data) : baseAlgebra data))) := by
    simpa only [StarAlgEquiv.symm_apply_apply] using h
  change baseToCorona data (r : baseAlgebra data) =
    backwardCoronaHom data
      (((baseUnitaryHom data).comp (edgeHom phi) s :
        unitary (baseAlgebra data)) : baseAlgebra data)
  exact h'

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
