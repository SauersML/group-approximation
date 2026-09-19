import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.ShulmanCoronaSquareRootSequence

/-!
# Positivity of a square-root sequence in a C-star product corona
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ)

noncomputable local instance quotientNonnegCoordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance quotientNonnegCoordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

noncomputable local instance quotientNonnegCoronaPartialOrder :
    PartialOrder (CStarProductCorona A l) :=
  CStarAlgebra.spectralOrder (CStarProductCorona A l)

noncomputable local instance quotientNonnegCoronaStarOrderedRing :
    StarOrderedRing (CStarProductCorona A l) :=
  CStarAlgebra.spectralOrderedRing (CStarProductCorona A l)

theorem quotient_sqrtSequence_nonneg
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    0 ≤ cStarProductCoronaQuotient A l (sqrtSequence A a ha) := by
  let r := sqrtSequence A a ha
  have hr : ∀ n, 0 ≤ r n := sqrtSequence_nonneg A a ha
  let z := sqrtSequence A r hr
  have hzSelf : IsSelfAdjoint z := sqrtSequence_isSelfAdjoint A r hr
  rw [show sqrtSequence A a ha = z * z by
    exact (sqrtSequence_mul_self A r hr).symm]
  rw [map_mul]
  nth_rw 1 [← hzSelf.star_eq]
  rw [map_star]
  exact star_mul_self_nonneg _

end


end ShulmanCoronaSquareRoot
end GroupApproximation
