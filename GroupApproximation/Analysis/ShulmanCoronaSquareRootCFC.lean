import GroupApproximation.Analysis.ShulmanCoronaSquareRootRealCFC
import GroupApproximation.Analysis.ShulmanCoronaNontrivial

/-!
# Continuous-functional-calculus data for a C-star product corona
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ) [l.NeBot]

noncomputable local instance cfcCoronaPartialOrder :
    PartialOrder (CStarProductCorona A l) :=
  CStarAlgebra.spectralOrder (CStarProductCorona A l)

noncomputable local instance cfcCoronaStarOrderedRing :
    StarOrderedRing (CStarProductCorona A l) :=
  CStarAlgebra.spectralOrderedRing (CStarProductCorona A l)

noncomputable local instance cfcCoronaRealCFC :
    NonUnitalContinuousFunctionalCalculus ℝ
      (CStarProductCorona A l) IsSelfAdjoint :=
  coronaRealCFC A l

noncomputable abbrev coronaNonnegSpectrum :
    NonnegSpectrumClass ℝ (CStarProductCorona A l) :=
  @CStarAlgebra.instNonnegSpectrumClass'
    (CStarProductCorona A l) inferInstance
    (cfcCoronaPartialOrder A l) (cfcCoronaStarOrderedRing A l)

noncomputable local instance cfcCoronaNonnegSpectrum :
    NonnegSpectrumClass ℝ (CStarProductCorona A l) :=
  coronaNonnegSpectrum A l

noncomputable abbrev coronaNNRealCFC :
    NonUnitalContinuousFunctionalCalculus NNReal
      (CStarProductCorona A l)
      (fun a : CStarProductCorona A l ↦ 0 ≤ a) := by
  exact Nonneg.instNonUnitalContinuousFunctionalCalculus
    (A := CStarProductCorona A l)

end


end ShulmanCoronaSquareRoot
end GroupApproximation
