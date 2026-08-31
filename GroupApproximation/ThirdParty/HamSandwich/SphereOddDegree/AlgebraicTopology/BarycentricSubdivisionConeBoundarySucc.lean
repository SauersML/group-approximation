import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundaryZero

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-
**Boundary of the cone (successor degree).** For `σ` of degree `m+1`,
`∂ Cone_v([σ]) = [σ] - Cone_v(∂[σ])`.
-/
theorem singularBoundary_coneGenerator_succ (R : Type) [CommRing R] (n m : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (m + 1)) :
    (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom (coneGenerator R n (m + 1) v σ)
      = chainGenerator R (TopCat.of (Delta n)) (m + 1) σ
        - (coneLinearMap R n m v).hom
            ((singularBoundary R (TopCat.of (Delta n)) m).hom
              (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) := by
  convert singularBoundary_chainGenerator_formula R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } ( m + 1 ) ( coneSimplex n ( m + 1 ) v σ ) using 1;
  rw [ Fin.sum_univ_succ ];
  simp +decide [ singularBoundary_chainGenerator_formula, coneSimplex_face_zero, coneSimplex_face_succ, coneLinearMap_generator ];
  simp +decide [ pow_succ', neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg ];
  rfl
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

