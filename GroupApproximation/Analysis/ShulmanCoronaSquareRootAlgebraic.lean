import GroupApproximation.Analysis.ShulmanCoronaSquareRootSequenceDef
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Algebraic properties of coordinatewise square roots
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]

noncomputable local instance algebraicCoordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance algebraicCoordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

/-- Squaring the coordinatewise positive square root recovers the sequence. -/
theorem sqrtSequence_mul_self
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    sqrtSequence A a ha * sqrtSequence A a ha = a := by
  apply lp.ext
  funext n
  exact CFC.sqrt_mul_sqrt_self (a n) (ha n)

/-- The coordinatewise square-root sequence is selfadjoint. -/
theorem sqrtSequence_isSelfAdjoint
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    IsSelfAdjoint (sqrtSequence A a ha) := by
  apply lp.ext
  funext n
  exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a n))).star_eq

end


end ShulmanCoronaSquareRoot
end GroupApproximation
