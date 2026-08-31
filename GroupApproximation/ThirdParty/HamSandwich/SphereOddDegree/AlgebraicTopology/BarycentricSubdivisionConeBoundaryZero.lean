import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeChainDefs

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-! ## 8. The boundary formula -/

/-
**Boundary of the cone (base degree).** In degree `0`,
`∂ Cone_v([σ]) = [σ] - [const_v]`.
-/
theorem singularBoundary_coneGenerator_zero (R : Type) [CommRing R] (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    (singularBoundary R (TopCat.of (Delta n)) 0).hom (coneGenerator R n 0 v σ)
      = chainGenerator R (TopCat.of (Delta n)) 0 σ
        - chainGenerator R (TopCat.of (Delta n)) 0 (constSimplex0 n v) := by
  rw [coneGenerator, singularBoundary_chainGenerator_formula]
  rw [Fin.sum_univ_two]
  norm_num [sub_eq_add_neg]
  rw [coneSimplex_face_zero, coneSimplex_face_one_zero]
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
