import GroupApproximation.Analysis.PolarLiftingGeneralCStar

/-!
# Algebraic coordinate evaluation on a bounded C-star product
-/

namespace GroupApproximation
namespace PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]

/-- Evaluation at one coordinate, before recording preservation of `star`. -/
def boundedCStarSequenceAlgEval (n : ℕ) :
    BoundedCStarSequence A →ₙₐ[ℂ] A n where
  toFun a := a n
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem boundedCStarSequenceAlgEval_apply
    (n : ℕ) (a : BoundedCStarSequence A) :
    boundedCStarSequenceAlgEval A n a = a n :=
  rfl

end


end PolarLiftingGeneralCStar
end GroupApproximation
