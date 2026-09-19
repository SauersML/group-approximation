import GroupApproximation.Analysis.BoundedCStarSequenceEvaluationDef

/-!
# Coordinate evaluation on a bounded C-star product
-/

namespace GroupApproximation
namespace PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]

/-- Coordinate evaluation is contractive, hence continuous. -/
theorem continuous_boundedCStarSequenceEval (n : ℕ) :
    Continuous (boundedCStarSequenceEval A n) :=
  (lp.evalCLM ℂ A ⊤ n).continuous

end

end PolarLiftingGeneralCStar
end GroupApproximation
