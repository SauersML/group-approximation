import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexDefs

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-
**Apex face of `coneSimplex`.** The `0`-th boundary face of the cone of `σ`
is `σ`.
-/
theorem coneSimplex_face_zero (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k 0 (coneSimplex n k v σ) = σ := by
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, coneSimplex_continuousMap]
  apply ContinuousMap.ext
  intro y
  exact congrFun
    (cone_face_zero v
      (fun z => singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ z)) y
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
