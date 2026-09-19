import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeGeometry
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricBoundaryCancellation

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-! ## 6. The cone on singular simplices and chains of `Δⁿ` -/

/-- The cone of a singular `k`-simplex of `Δⁿ` over `v`, as a singular
`(k+1)`-simplex of `Δⁿ`. -/
noncomputable def coneSimplex (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplices (TopCat.of (Delta n)) (k + 1) :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) (k + 1)
    (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ))

/-- The continuous map underlying `coneSimplex`. -/
theorem coneSimplex_continuousMap (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)
      = affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ) := by
  rw [coneSimplex, singularSimplexAsContinuousMap, continuousMapAsSingularSimplex,
    Equiv.apply_symm_apply]

/-- The `0`-simplex with value `v` at every vertex. -/
noncomputable def constSimplex0 (n : ℕ) (v : Delta n) :
    singularSimplices (TopCat.of (Delta n)) 0 :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) 0
    (ContinuousMap.const (Delta 0) v)
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

