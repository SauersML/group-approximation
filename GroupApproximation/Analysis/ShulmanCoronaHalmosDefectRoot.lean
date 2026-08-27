import GroupApproximation.Analysis.ShulmanCoronaHalmosArgumentCommutator

/-! Asymptotic commutators of the two Halmos defect roots. -/

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

/-- The left Halmos defect roots asymptotically commute with `b`. -/
theorem isNull_commutator_leftDefectRoot
    (x b : BoundedCStarSequence A) (hx : ∀ n, ‖x n‖ ≤ 1)
    (hxComm : IsNullCStarSequence A l (x * b - b * x))
    (hxStarComm : IsNullCStarSequence A l (star x * b - b * star x)) :
    IsNullCStarSequence A l
      (sqrtSequence A (leftArgument A x) (leftArgument_nonneg A x hx) * b -
        b * sqrtSequence A (leftArgument A x) (leftArgument_nonneg A x hx)) :=
  isNull_commutator_sqrtSequence A l (leftArgument A x) b
    (leftArgument_nonneg A x hx)
    (isNull_commutator_leftArgument A l x b hxComm hxStarComm)

/-- The right Halmos defect roots asymptotically commute with `b`. -/
theorem isNull_commutator_rightDefectRoot
    (x b : BoundedCStarSequence A) (hx : ∀ n, ‖x n‖ ≤ 1)
    (hxComm : IsNullCStarSequence A l (x * b - b * x))
    (hxStarComm : IsNullCStarSequence A l (star x * b - b * star x)) :
    IsNullCStarSequence A l
      (sqrtSequence A (rightArgument A x) (rightArgument_nonneg A x hx) * b -
        b * sqrtSequence A (rightArgument A x) (rightArgument_nonneg A x hx)) :=
  isNull_commutator_sqrtSequence A l (rightArgument A x) b
    (rightArgument_nonneg A x hx)
    (isNull_commutator_rightArgument A l x b hxComm hxStarComm)
end

end ShulmanCoronaHalmosCommutator
end GroupApproximation
