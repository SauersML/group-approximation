import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Coordinatewise positive square roots in a bounded C-star product
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]

noncomputable local instance coordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance coordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

/-- The coordinatewise positive square root of a bounded positive sequence is
again bounded. -/
def sqrtSequence (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    BoundedCStarSequence A :=
  ⟨fun n ↦ CFC.sqrt (a n), memℓp_infty ⟨√‖a‖, by
    rintro _ ⟨n, rfl⟩
    change ‖CFC.sqrt (a n)‖ ≤ √‖a‖
    rw [CFC.norm_sqrt (a n) (ha n)]
    exact Real.sqrt_le_sqrt (boundedCStarSequence_coord_norm_le A a n)⟩⟩

@[simp] theorem sqrtSequence_apply
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    sqrtSequence A a ha n = CFC.sqrt (a n) :=
  rfl

/-- The coordinatewise square-root sequence is positive in every coordinate. -/
theorem sqrtSequence_nonneg
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ sqrtSequence A a ha n :=
  CFC.sqrt_nonneg _

end

end ShulmanCoronaSquareRoot
end GroupApproximation
