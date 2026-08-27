import GroupApproximation.Manuscript.MFRecognition.HNNTraceCovariantRepresentation

/-!
# The faithful HNN group lift
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open ReducedGroupCStarTrace

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The base-group representation inside the universal HNN algebra. -/
def universalBaseUnitary (data : CoronaConjugator G S T phi A X) :
    G →* unitary (universalHNN data) :=
  (unitaryMapOfStarAlgHom (universalBase data)).comp (baseUnitaryHom data)

/-- The defining HNN covariance relation holds inside the universal algebra. -/
theorem universalBaseUnitary_covariance
    (data : CoronaConjugator G S T phi A X) (s : S) :
    universalStable data * universalBaseUnitary data (s : G) =
      universalBaseUnitary data ((phi s : T) : G) * universalStable data := by
  apply Subtype.ext
  have h := universalCStarHNN_covariance (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data)
    ((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
      sourceEdgeAlgebra data)
  rw [edgeIsomorphism_generator] at h
  exact h

/-- The group homomorphism `j : R → U(U)` supplied by the HNN relations. -/
def groupLift (data : CoronaConjugator G S T phi A X) :
    HNNExtension G S T phi →* unitary (universalHNN data) :=
  universalCStarHNNGroupLift (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
    (edgeIsomorphism data) phi (universalBaseUnitary data)
    (universalBaseUnitary_covariance data)

@[simp] theorem groupLift_of (data : CoronaConjugator G S T phi A X) (g : G) :
    groupLift data (HNNExtension.of g) = universalBaseUnitary data g :=
  universalCStarHNNGroupLift_of _ _ _ _ _ _ g

@[simp] theorem groupLift_t (data : CoronaConjugator G S T phi A X) :
    groupLift data HNNExtension.t = universalStable data :=
  universalCStarHNNGroupLift_t _ _ _ _ _ _

/-- Evaluation of `j` under `σ` is the left regular representation. -/
theorem groupLiftEval_eq_regular
    (data : CoronaConjugator G S T phi A X) :
    universalCStarHNNGroupLiftEval (sourceEdgeAlgebra data)
        (targetEdgeAlgebra data) (edgeIsomorphism data) phi
        (reducedCovariantRepresentation data)
        (universalBaseUnitary data)
        (universalBaseUnitary_covariance data) =
      reducedLeftRegularUnitaryHom (HNNExtension G S T phi) := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine MonoidHom.ext fun g ↦ ?_
    apply Subtype.ext
    show sigma data
        ((groupLift data (HNNExtension.of g) : unitary (universalHNN data)) :
          universalHNN data) =
      reducedLeftRegular (HNNExtension G S T phi) (HNNExtension.of g)
    rw [groupLift_of]
    exact sigmaZero_apply data g
  · apply Subtype.ext
    show sigma data
        ((groupLift data HNNExtension.t : unitary (universalHNN data)) :
          universalHNN data) =
      reducedLeftRegular (HNNExtension G S T phi) HNNExtension.t
    exact congrArg
      (fun u : unitary (universalHNN data) ↦
        sigma data (u : universalHNN data))
      (groupLift_t data)

/-- Since `σ ∘ j` is regular, the group lift `j` is injective. -/
theorem groupLift_injective
    (data : CoronaConjugator G S T phi A X) :
    Function.Injective (groupLift data) := by
  apply universalCStarHNN_groupLift_injective (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data) phi
    (reducedCovariantRepresentation data) (universalBaseUnitary data)
    (universalBaseUnitary_covariance data)
  rw [groupLiftEval_eq_regular]
  exact reducedLeftRegularUnitaryHom_injective (HNNExtension G S T phi)

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
