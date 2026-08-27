import GroupApproximation.Manuscript.MFRecognition.HNNTraceGroupLift

/-!
# `thm:hnn-permanence`, Step 3: the tracial realization

The trace-specific analytic work is split into three direct modules:

* `HNNTraceReducedFactorization` transports the regular trace to the represented
  base algebra and factors its representation through `C*_r(G)`;
* `HNNTraceReducedSubgroup` constructs the reduced C-star map induced by the
  injective base-group map into the HNN extension and proves countability;
* `HNNTraceCovariantRepresentation` proves edge density, covariance, and the
  faithful group lift into the universal C-star HNN algebra.

This file performs only the final trace pullback and realization assembly.  Its
sole ordinary premise is the concrete MF property of the universal HNN algebra.
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

/-- The pullback of the canonical trace `τ_R` of `C*_r(R)` along `σ`. -/
def universalTrace (data : CoronaConjugator G S T phi A X) :
    TracialState (universalHNN data) :=
  ((canonicalFaithfulTracialState
    (HNNExtension G S T phi)).toTracialState).compStarAlgHom
      (sigma data)

/-- Printed: *"`τ'(j(r)) = τ_R(λ_R(r)) = 0` for `r ≠ 1`."* -/
theorem universalTrace_regular
    (data : CoronaConjugator G S T phi A X)
    (r : HNNExtension G S T phi) (hr : r ≠ 1) :
    universalTrace data
        (((groupLift data r : unitary (universalHNN data)) :
          universalHNN data)) = 0 := by
  have hlambda : sigma data
      (((groupLift data r : unitary (universalHNN data)) :
        universalHNN data)) =
      reducedLeftRegular (HNNExtension G S T phi) r := by
    have h := congrArg (fun f : HNNExtension G S T phi →*
        unitary (ReducedGroupCStar (HNNExtension G S T phi)) ↦ f r)
      (groupLiftEval_eq_regular data)
    exact congrArg Subtype.val h
  show ((canonicalFaithfulTracialState
      (HNNExtension G S T phi)).toTracialState)
      (sigma data
        (((groupLift data r : unitary (universalHNN data)) :
          universalHNN data))) = 0
  rw [hlambda]
  exact canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one
    (HNNExtension G S T phi) hr

/-- The tracial MF realization of the HNN extension generated inside the
universal HNN algebra. -/
def hnnRegularRealization [Countable G]
    (data : CoronaConjugator G S T phi A X)
    (hMF : IsMFAlgebra (universalHNN data)) :
    RegularRealizationData (HNNExtension G S T phi)
      (groupGeneratedCStar (groupLift data)) := by
  letI : Countable (HNNExtension G S T phi) :=
    hnnExtension_countable G S T phi
  exact generatedRegularRealization
    hMF.2 (groupLift data) (universalTrace data)
    (fun r hr ↦ universalTrace_regular data r hr)

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
