import GroupApproximation.Analysis.ShulmanCoronaSquareRootQuotientNonneg
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Complex continuous functional calculus on a C-star product corona
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ)

noncomputable abbrev coronaComplexCFC :
    NonUnitalContinuousFunctionalCalculus ℂ
      (CStarProductCorona A l) IsStarNormal :=
  (IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus
    (A := CStarProductCorona A l)).toNonUnitalContinuousFunctionalCalculus

end


end ShulmanCoronaSquareRoot
end GroupApproximation
