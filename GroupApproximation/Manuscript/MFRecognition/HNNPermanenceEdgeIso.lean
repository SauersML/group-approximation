import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceEdgeAmbientEquiv

/-!
# The edge isomorphism in the HNN permanence proof
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Printed: *"Conjugation by `W` restricts to a `*`-isomorphism
`Θ : B₀ → B₁` carrying `ιρ(s)` to `ιρ(θ(s))`."* -/
theorem exists_edgeIsomorphism (data : CoronaConjugator G S T phi A X) :
    ∃ Θ : sourceEdgeAlgebra data ≃⋆ₐ[ℂ] targetEdgeAlgebra data,
      (∀ b : sourceEdgeAlgebra data,
          Unitary.conjStarAlgAut ℂ (Corona X) data.W
              ((b : baseAlgebra data) : Corona X) =
            (((Θ b : targetEdgeAlgebra data) : baseAlgebra data) :
              Corona X)) ∧
        ∀ s : S,
          Θ ((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
              sourceEdgeAlgebra data) =
            ((targetGenerator data s : unitary (targetEdgeAlgebra data)) :
              targetEdgeAlgebra data) := by
  refine ⟨constructedEdgeIsomorphism data, ?_, ?_⟩
  · exact constructedEdgeIsomorphism_conj data
  · exact constructedEdgeIsomorphism_generator data

/-- The edge isomorphism `Θ` of the printed proof. -/
def edgeIsomorphism (data : CoronaConjugator G S T phi A X) :
    sourceEdgeAlgebra data ≃⋆ₐ[ℂ] targetEdgeAlgebra data :=
  (exists_edgeIsomorphism data).choose

/-- `Θ` is conjugation by `W`. -/
theorem edgeIsomorphism_conj (data : CoronaConjugator G S T phi A X)
    (b : sourceEdgeAlgebra data) :
    Unitary.conjStarAlgAut ℂ (Corona X) data.W
        ((b : baseAlgebra data) : Corona X) =
      (((edgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data) : Corona X) :=
  (exists_edgeIsomorphism data).choose_spec.1 b

/-- `Θ` carries `ιρ(s)` to `ιρ(θ(s))`. -/
theorem edgeIsomorphism_generator (data : CoronaConjugator G S T phi A X)
    (s : S) :
    edgeIsomorphism data
        ((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
          sourceEdgeAlgebra data) =
      ((targetGenerator data s : unitary (targetEdgeAlgebra data)) :
        targetEdgeAlgebra data) :=
  (exists_edgeIsomorphism data).choose_spec.2 s

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
