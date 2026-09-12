import GroupApproximation.Analysis.AdjointDefectEstimate
import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.ExchangePrerequisite
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransport
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints

/-!
# Sentence closure for the mathematical comparison paragraphs

Exact row-numbered wrappers for census rows 89--90 and 93--94.  Rows 86--88,
91--92, and 95--97 contain historical or literature comparisons and are not
asserted as new Lean propositions here.  Rows 79--85 and 98--99 are already
covered by the dedicated camouflage and commutant closure modules.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u

noncomputable section

open scoped Matrix.Norms.L2Operator

/-- **Sentence 89.**  Operator-norm asymptotic multiplicativity makes the
coordinatewise adjoint actions asymptotically multiplicative in the second
matrix model, with the printed dimension-square count. -/
theorem manuscriptSentence89_operatorNorm_builds_adjointRepresentation
    {G : Type u} [Group G] (A : OpAlmostRepresentation G) :
    (∀ (Z : FiniteModel) (U V : Matrix Z Z ℂ),
        U ∈ Matrix.unitaryGroup Z ℂ → V ∈ Matrix.unitaryGroup Z ℂ →
        ∀ X : Matrix Z Z ℂ,
          ‖adConj U X - adConj V X‖ ≤ 2 * ‖U - V‖ * ‖X‖) ∧
      (∀ g h : G, ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
        ∀ X : Matrix (A.model n) (A.model n) ℂ,
          ‖adConj (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) X -
              adConj (A.map n g : Matrix (A.model n) (A.model n) ℂ)
                (adConj (A.map n h : Matrix (A.model n) (A.model n) ℂ) X)‖
            ≤ epsilon * ‖X‖) ∧
      (∀ n : ℕ, Fintype.card (A.adjoint.naturalizeCoordinates.model n) =
        Fintype.card (A.model n) ^ 2) :=
  A.printedAdjointParagraph

/-- **Sentence 90.**  The Kazhdan transport theorem controls the asymptotic
Hilbert--Schmidt commutant, and the normal-Kazhdan theorem converts the shadow
residual conclusion into the genuine MF radical conclusion. -/
theorem manuscriptSentence90_transport_and_normalKazhdanRadical :
    OneSidedKazhdanTransport ∧ NormalKazhdanRadical :=
  ⟨manuscriptOneSidedKazhdanTransport, manuscriptNormalKazhdanRadical⟩

/-- **Sentence 93.**  The concrete binary Leavitt algebra satisfies the
right-exchange property used in the comparison paragraph. -/
theorem manuscriptSentence93_binaryLeavitt_is_exchange :
    ExchangePrerequisite.HasRightExchange RankTwelveEndpoint.R :=
  BinaryLeavitt.hasRightExchange (ZMod 2)

/-- **Sentence 94.**  The center of the concrete binary Leavitt algebra is
exactly its base field. -/
theorem manuscriptSentence94_binaryLeavitt_center_is_baseField :
    Subalgebra.center (ZMod 2) RankTwelveEndpoint.R = ⊥ :=
  BinaryLeavitt.center_eq_bot (ZMod 2)

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
