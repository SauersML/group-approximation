import GroupApproximation.Analysis.BoundedCStarSequenceAlgebraEvaluation

/-!
# Coordinate evaluation on a bounded C-star product
-/

namespace GroupApproximation
namespace PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]

/-- Evaluation at one coordinate of a bounded C-star sequence. -/
def boundedCStarSequenceEval (n : ℕ) :
    BoundedCStarSequence A →⋆ₙₐ[ℂ] A n :=
  { toNonUnitalAlgHom := boundedCStarSequenceAlgEval A n
    map_star' := fun _ ↦ rfl }

@[simp] theorem boundedCStarSequenceEval_apply
    (n : ℕ) (a : BoundedCStarSequence A) :
    boundedCStarSequenceEval A n a = a n :=
  rfl

end

end PolarLiftingGeneralCStar
end GroupApproximation
