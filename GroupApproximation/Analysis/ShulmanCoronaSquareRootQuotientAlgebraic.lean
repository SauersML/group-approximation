import GroupApproximation.Analysis.ShulmanCoronaSquareRootQuotientNonneg

/-!
# Algebraic square-root identities in a C-star product corona
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ)

noncomputable local instance quotientAlgebraicCoordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance quotientAlgebraicCoordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

theorem quotient_sqrtSequence_mul_self
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    cStarProductCoronaQuotient A l (sqrtSequence A a ha) *
        cStarProductCoronaQuotient A l (sqrtSequence A a ha) =
      cStarProductCoronaQuotient A l a := by
  rw [← map_mul, sqrtSequence_mul_self A a ha]

end


end ShulmanCoronaSquareRoot
end GroupApproximation
