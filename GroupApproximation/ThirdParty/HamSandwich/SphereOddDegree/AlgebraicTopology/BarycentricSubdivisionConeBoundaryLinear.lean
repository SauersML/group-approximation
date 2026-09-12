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
  apply Sigma.hom_ext
  intro σ
  ext
  change
    (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom
        ((coneLinearMap R n (m + 1) v).hom
          (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ))
      + (coneLinearMap R n m v).hom
          ((singularBoundary R (TopCat.of (Delta n)) m).hom
            (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ))
      = chainGenerator R (TopCat.of (Delta n)) (m + 1) σ
  rw [coneLinearMap_generator, singularBoundary_coneGenerator_succ]
  abel
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
