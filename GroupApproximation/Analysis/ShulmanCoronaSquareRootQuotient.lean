import GroupApproximation.Analysis.ShulmanCoronaSquareRootCFC
import GroupApproximation.Analysis.ShulmanCoronaSquareRootQuotientAlgebraic

/-!
# Naturality of positive square roots in a C-star product corona
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ) [l.NeBot]

noncomputable local instance quotientCoordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance quotientCoordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

noncomputable local instance quotientCoronaPartialOrder :
    PartialOrder (CStarProductCorona A l) :=
  quotientNonnegCoronaPartialOrder A l

noncomputable local instance quotientCoronaStarOrderedRing :
    StarOrderedRing (CStarProductCorona A l) :=
  quotientNonnegCoronaStarOrderedRing A l

noncomputable local instance quotientCoronaComplexCFC :
    NonUnitalContinuousFunctionalCalculus ℂ
      (CStarProductCorona A l) IsStarNormal :=
  coronaComplexCFC A l

noncomputable local instance quotientCoronaRealCFC :
    NonUnitalContinuousFunctionalCalculus ℝ
      (CStarProductCorona A l) IsSelfAdjoint :=
  coronaRealCFC A l

noncomputable local instance quotientCoronaNonnegSpectrum :
    NonnegSpectrumClass ℝ (CStarProductCorona A l) :=
  coronaNonnegSpectrum A l

noncomputable local instance quotientCoronaNNRealCFC :
    NonUnitalContinuousFunctionalCalculus NNReal
      (CStarProductCorona A l)
      (fun a : CStarProductCorona A l ↦ 0 ≤ a) :=
  coronaNNRealCFC A l

omit [l.NeBot] in
/-- The corona class of the coordinatewise positive square-root sequence is
the positive square root of the class of the original sequence. -/
theorem quotient_sqrtSequence
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    cStarProductCoronaQuotient A l (sqrtSequence A a ha) =
      CFC.sqrt (cStarProductCoronaQuotient A l a) := by
  let q := cStarProductCoronaQuotient A l
  symm
  apply CFC.sqrt_unique
  · exact quotient_sqrtSequence_mul_self A l a ha
  · exact quotient_sqrtSequence_nonneg A l a ha

end


end ShulmanCoronaSquareRoot
end GroupApproximation
