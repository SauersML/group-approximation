import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundarySucc

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-
**The cone chain-homotopy identity (successor degree).**
`∂ ∘ Cone + Cone ∘ ∂ = id` on `C_{m+1}(Δⁿ; R)`.
-/
theorem singularBoundary_coneLinearMap (R : Type) [CommRing R] (n m : ℕ) (v : Delta n) :
    coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)
        + singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v
      = 𝟙 (singularChainGroup R (TopCat.of (Delta n)) (m + 1)) := by
  apply Sigma.hom_ext;
  intro σ; ext; simp +decide [ ModuleCat.hom_comp, ModuleCat.hom_add, LinearMap.add_apply ] ;
  convert congr_arg ( fun x => x + ( coneLinearMap R n m v ).hom ( ( singularBoundary R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } m ).hom ( chainGenerator R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } ( m + 1 ) σ ) ) ) ( singularBoundary_coneGenerator_succ R n m v σ ) using 1 ; ring!;
  · convert rfl;
    convert coneLinearMap_generator R n ( m + 1 ) v σ |> Eq.symm;
  · simp +decide [ chainGenerator ];
    rfl
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

