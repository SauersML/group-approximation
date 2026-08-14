import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.NormMFConsequences

/-!
# A closed finite operator-norm obstruction for the literal group

This is the premise-free specialization of compactness-based uniform
invisibility to the displayed marked word.  It is quantitative in the
mathematical sense that one positive defect budget and one finite test set
work in every matrix dimension.  It is not yet an effective computation of
that budget or test set.
-/

namespace GroupApproximation
namespace LiteralUniformObstruction

open Matrix
open scoped Matrix.Norms.L2Operator
open LiteralNonMFPresentation

/-- There is one positive multiplicative-defect threshold and one finite
test set that force the literal marked word into the open operator-norm unit
ball about the identity, uniformly in the matrix dimension. -/
theorem literal_uniform_operatorNorm_obstruction :
    ∃ (δ : ℝ) (F₀ : Finset MarkedGroup), 0 < δ ∧
      ∀ (Y : FiniteModel)
        (φ : MarkedGroup → Matrix.unitaryGroup Y ℂ),
        (∀ g ∈ F₀, ∀ h ∈ F₀,
          ‖(φ (g * h) : Matrix Y Y ℂ) -
            (φ g : Matrix Y Y ℂ) * φ h‖ ≤ δ) →
        ‖(φ mark : Matrix Y Y ℂ) - 1‖ < 1 := by
  exact uniform_invisibility
    LiteralNonMFEndpoint.literal_mark_normMFInvisible 1 (by norm_num)

end LiteralUniformObstruction
end GroupApproximation
