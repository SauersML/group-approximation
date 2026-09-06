import GroupApproximation.Analysis.LIXStageAlgebra
import GroupApproximation.Analysis.LIXConnectingMapPoints
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

set_option autoImplicit false

/-!
# Separability of the stage algebras

`Analysis/LIXLimitSeparable.lean`'s `CStarTower.separableSpace_limit` turns
`∀ n, SeparableSpace (A n)` into separability of the limit, which is the one bonus conjunct
of the STW LIX endpoint.  For the stage algebras it is instance plumbing rather than
mathematics, so it lives in its own small file:

* `X_n` is second countable — `S⁴` as a subtype of a finite-dimensional normed space, and
  each `ℂP^{r_j}` as a subtype of a matrix space, with `Analysis/LIXConnectingMapPoints.lean`
  supplying both;
* `CStarMatrix ι ι ℂ` is second countable, since its topology is `inferInstanceAs` the
  entrywise one;
* hence `C(X_n, CStarMatrix ι ι ℂ)` is second countable, by Mathlib's
  `ContinuousMap.instSecondCountableTopology` for a locally compact second countable domain;
* second countability passes to the subtype `A_n`, and second countable implies separable.

The middle step is the one that could have failed: `C(X, Y)` carries the compact-open
topology, while the C-star structure on `C(X, A)` for compact `X` is the uniform one.  They
agree for compact `X`, and Mathlib builds the metric so that the instances agree, so the
chain goes through with no `replaceTopology` on our side.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix ComplexOrder CStarAlgebra

noncomputable section

instance instSecondCountableCStarMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (CStarMatrix ι ι ℂ) :=
  inferInstanceAs (SecondCountableTopology (Matrix ι ι ℂ))

instance instSecondCountableSectionAlgebra (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] (ι : Type*) [Fintype ι]
    [DecidableEq ι] : SecondCountableTopology (SectionAlgebra X ι) :=
  inferInstanceAs (SecondCountableTopology C(X, CStarMatrix ι ι ℂ))

instance instSecondCountableBaseX (i : ℕ) : SecondCountableTopology (baseX i) :=
  inferInstance

/-- **The stage algebras are separable.**  This is the hypothesis of
`LIX.CStarTower.separableSpace_limit`. -/
instance instSeparableSpaceStageAlgebra (i : ℕ) :
    TopologicalSpace.SeparableSpace (StageAlgebra i) :=
  inferInstance

/-- The family form, for the tower. -/
instance instSeparableSpaceStageAlgebraPi :
    ∀ n : ℕ, TopologicalSpace.SeparableSpace (StageAlgebra n) := fun _ => inferInstance

end

end STW59
end GroupApproximation
