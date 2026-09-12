import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceSucc

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-
**The second face of a 1-dimensional cone.** The `1`-st boundary face of the
cone of a `0`-simplex `σ` is the simplex with value `v` at every vertex.
-/
theorem coneSimplex_face_one_zero (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) 0 1 (coneSimplex n 0 v σ)
      = constSimplex0 n v := by
  apply singularSimplices_ext;
  rw [ faceSimplex_continuousMap, coneSimplex_continuousMap ];
  ext y; simp [affineConeContinuousMap_apply, affineConeMap_coord];
  simp +decide [ cofaceTop, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply ];
  simp +decide [ Finset.filter_singleton, Fin.succAbove ];
  unfold singularSimplexAsContinuousMap constSimplex0; aesop;
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

