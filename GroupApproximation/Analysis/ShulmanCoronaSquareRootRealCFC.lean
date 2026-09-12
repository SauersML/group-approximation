import GroupApproximation.Analysis.ShulmanCoronaSquareRootComplexCFC

/-!
# Real continuous functional calculus on a C-star product corona
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ)

noncomputable abbrev coronaRealCFC :
    NonUnitalContinuousFunctionalCalculus ℝ
      (CStarProductCorona A l) IsSelfAdjoint := by
  letI := coronaComplexCFC A l
  exact IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    (A := CStarProductCorona A l)

end


end ShulmanCoronaSquareRoot
end GroupApproximation
