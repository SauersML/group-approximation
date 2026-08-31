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
  have h_cont : (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)).comp (cofaceTop k 0) = singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ := by
    ext y;
    convert congr_fun ( cone_face_zero v ( fun y => singularSimplexAsContinuousMap ( TopCat.of ( Delta n ) ) k σ y ) ) y |> congr_arg ( fun f => f ‹_› ) using 1;
  apply singularSimplices_ext;
  convert h_cont using 1
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

