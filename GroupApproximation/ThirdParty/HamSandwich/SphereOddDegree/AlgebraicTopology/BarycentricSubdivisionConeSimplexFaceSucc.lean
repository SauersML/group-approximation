/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceZero

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-
**Internal faces of `coneSimplex`.** The `(j+1)`-th boundary face of the cone
of `σ` is the cone of the `j`-th boundary face of `σ`.
-/
theorem coneSimplex_face_succ (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (k + 1)) (j : Fin (k + 1 + 1)) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) (k + 1) j.succ (coneSimplex n (k + 1) v σ)
      = coneSimplex n k v (AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k j σ) := by
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, coneSimplex_continuousMap,
    coneSimplex_continuousMap, faceSimplex_continuousMap]
  apply ContinuousMap.ext
  intro y
  exact congrFun
    (cone_face_succ v
      (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) σ) j) y
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
