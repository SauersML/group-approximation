import GroupApproximation.Analysis.ShulmanCoronaSquareRootCommutator
import GroupApproximation.Analysis.ShulmanHalmosDilation

/-! Defect arguments for the coordinatewise Halmos dilation. -/

namespace GroupApproximation
namespace ShulmanCoronaHalmosCommutator

open Filter PolarLiftingGeneralCStar ShulmanCoronaSquareRoot

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ)

noncomputable local instance (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

/-- The coordinatewise left defect argument `1 - x x*`. -/
def leftArgument (x : BoundedCStarSequence A) : BoundedCStarSequence A :=
  1 - x * star x

/-- The coordinatewise right defect argument `1 - x* x`. -/
def rightArgument (x : BoundedCStarSequence A) : BoundedCStarSequence A :=
  1 - star x * x

@[simp] theorem leftArgument_apply (x : BoundedCStarSequence A) (n : ℕ) :
    leftArgument A x n = 1 - x n * star (x n) := by
  rfl

@[simp] theorem rightArgument_apply (x : BoundedCStarSequence A) (n : ℕ) :
    rightArgument A x n = 1 - star (x n) * x n := by
  rfl

/-- The left defect argument of a coordinatewise contraction is positive. -/
theorem leftArgument_nonneg (x : BoundedCStarSequence A)
    (hx : ∀ n, ‖x n‖ ≤ 1) (n : ℕ) :
    0 ≤ leftArgument A x n :=
  ShulmanHalmosDilation.left_defect_argument_nonneg (hx n)

/-- The right defect argument of a coordinatewise contraction is positive. -/
theorem rightArgument_nonneg (x : BoundedCStarSequence A)
    (hx : ∀ n, ‖x n‖ ≤ 1) (n : ℕ) :
    0 ≤ rightArgument A x n :=
  ShulmanHalmosDilation.right_defect_argument_nonneg (hx n)

end

end ShulmanCoronaHalmosCommutator
end GroupApproximation
