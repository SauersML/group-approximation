import GroupApproximation.Analysis.ShulmanCoronaHalmosDef

/-! Asymptotic commutators of the two Halmos defect arguments. -/

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

/-- The commutator of the left defect argument is null when the commutators
of `x` and `x*` are null. -/
theorem isNull_commutator_leftArgument
    (x b : BoundedCStarSequence A)
    (hxComm : IsNullCStarSequence A l (x * b - b * x))
    (hxStarComm : IsNullCStarSequence A l (star x * b - b * star x)) :
    IsNullCStarSequence A l
      (leftArgument A x * b - b * leftArgument A x) := by
  have hformula :
      leftArgument A x * b - b * leftArgument A x =
        -(x * (star x * b - b * star x) +
          (x * b - b * x) * star x) := by
    dsimp only [leftArgument]
    noncomm_ring
  rw [hformula]
  exact (nullCStarSequenceIdeal A l).neg_mem
    ((nullCStarSequenceIdeal A l).add_mem
      (IsNullCStarSequence.mul_left A l x hxStarComm)
      (IsNullCStarSequence.mul_right A l hxComm (star x)))

/-- The commutator of the right defect argument is null under the same
hypotheses. -/
theorem isNull_commutator_rightArgument
    (x b : BoundedCStarSequence A)
    (hxComm : IsNullCStarSequence A l (x * b - b * x))
    (hxStarComm : IsNullCStarSequence A l (star x * b - b * star x)) :
    IsNullCStarSequence A l
      (rightArgument A x * b - b * rightArgument A x) := by
  have hformula :
      rightArgument A x * b - b * rightArgument A x =
        -(star x * (x * b - b * x) +
          (star x * b - b * star x) * x) := by
    dsimp only [rightArgument]
    noncomm_ring
  rw [hformula]
  exact (nullCStarSequenceIdeal A l).neg_mem
    ((nullCStarSequenceIdeal A l).add_mem
      (IsNullCStarSequence.mul_left A l (star x) hxComm)
      (IsNullCStarSequence.mul_right A l hxStarComm x))

end

end ShulmanCoronaHalmosCommutator
end GroupApproximation
