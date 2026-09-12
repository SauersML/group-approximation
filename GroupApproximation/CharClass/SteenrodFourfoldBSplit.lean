import GroupApproximation.CharClass.SteenrodFourfoldBCancel

/-!
# Splitting `B` by the bidegree of the cut

The assembly of the chain map needs a case analysis on the degree of the front
face: the left block of the Leibniz rule vanishes when that face is too small to
carry its share of the resolution index, and the boundary identity applies in two
different forms according to whether the index is zero.

That analysis is not available while the sum runs over the basis of `Φ₀(σ)` as
one `Finsupp`, because the bidegree varies across it.  So this file splits the
sum: `Φ₀(σ)` is itself a sum over bidegrees, and after that rewrite the front
degree is an explicit summation index and can be cased on.

This is the structural move the rest of the assembly rests on, and it costs
nothing: it is the definition of the diagonal plus the fact that a linear map
passes through a sum.

## Main result

* `compBPreGen_eq_double_sum` — `B` before the interchange, as a double sum over
  the resolution index and the bidegree of the cut.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- **`B` as a double sum.**  The outer index is the splitting of the resolution
index; the inner one is the bidegree of the cut of `σ`.  With both explicit, the
case analysis the Leibniz rule needs is available. -/
theorem compBPreGen_eq_double_sum (X : TopCat.{0}) (k i : ℕ) {N : ℕ}
    (σ : singularSimplices X N) :
    compBPreGen X k i σ
      = ∑ p ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (N + 1),
          Finsupp.linearCombination (ZMod 2) (compBPre X k i p N)
            (cellPair X N c (N - c) (steenrodDiag 0 c (N - c) σ)) := by
  unfold compBPreGen
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [phiZero_eq_phiAtDeg, phiAtDeg_eq_sum]
  exact map_sum (Finsupp.linearCombination (ZMod 2) (compBPre X k i p N)) _ _

end

end Steenrod
end CharClass
end GroupApproximation
