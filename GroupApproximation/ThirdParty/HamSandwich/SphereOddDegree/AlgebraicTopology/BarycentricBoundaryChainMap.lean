import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricBoundaryCancellation
import Mathlib

/-!
# Chain-level barycentric boundary commutation `∂ ∘ sd = sd ∘ ∂`

This file lifts the generator-level cancellation
`expandedBarycentricBoundaryCancellation` (from
`BarycentricBoundaryCancellation.lean`) to all singular chains.

The main results are:

* `barycentricSubdivisionLinearMap_commutes_boundary`: the morphism-level
  identity
  ```text
  sd ≫ ∂ = ∂ ≫ sd
  ```
  in the category of `R`-modules, i.e. degree-wise barycentric subdivision is a
  chain map for the singular boundary;
* `boundary_barycentricSubdivision_apply`: the pointwise version, `∂ (sd c) =
  sd (∂ c)` for every chain `c`.

## Degree convention

The singular boundary `singularBoundary R X n : C_{n+1} → C_n` is the degree
`(n+1) → n` differential of the alternating face map complex, with the project's
`(-1)^i` sign convention on faces.  The subdivision operator
`barycentricSubdivisionLinearMap R X n : C_n → C_n` is the signed sum over
permutations.  The commutation identity below relates
`barycentricSubdivisionLinearMap R X (n+1) ≫ singularBoundary R X n` with
`singularBoundary R X n ≫ barycentricSubdivisionLinearMap R X n`.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace AffineBarycentricSubdivision

/-- **Boundary commutation on a generator (chain-map form).**
On a basis generator `[σ]`, the singular boundary of its subdivision equals the
subdivision of its boundary. -/
theorem boundary_barycentricSubdivision_generator
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    (singularBoundary R X n).hom
        ((barycentricSubdivisionLinearMap R X (n + 1)).hom (chainGenerator R X (n + 1) σ))
      =
    (barycentricSubdivisionLinearMap R X n).hom
        ((singularBoundary R X n).hom (chainGenerator R X (n + 1) σ)) := by
  rw [barycentricSubdivisionLinearMap_generator]
  exact expandedBarycentricBoundaryCancellation R X n σ

/-- **Chain-level boundary commutation.** Degree-wise barycentric subdivision is
a chain map for the singular boundary:
```text
sd ≫ ∂ = ∂ ≫ sd.
```
This lifts the generator-level cancellation to all chains by coproduct
extensionality. -/
theorem barycentricSubdivisionLinearMap_commutes_boundary
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    barycentricSubdivisionLinearMap R X (n + 1) ≫ singularBoundary R X n
      = singularBoundary R X n ≫ barycentricSubdivisionLinearMap R X n := by
  symm
  apply Sigma.hom_ext
  intro σ
  ext
  change (barycentricSubdivisionLinearMap R X n).hom
      ((singularBoundary R X n).hom (chainGenerator R X (n + 1) σ)) =
    (singularBoundary R X n).hom
      ((barycentricSubdivisionLinearMap R X (n + 1)).hom
        (chainGenerator R X (n + 1) σ))
  exact (boundary_barycentricSubdivision_generator R X n σ).symm

/-- **Pointwise boundary commutation.** For every singular chain `c`,
```text
∂ (sd c) = sd (∂ c).
```
This is the element-level form of
`barycentricSubdivisionLinearMap_commutes_boundary`. -/
theorem boundary_barycentricSubdivision_apply
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : singularChainGroup R X (n + 1)) :
    (singularBoundary R X n).hom
        ((barycentricSubdivisionLinearMap R X (n + 1)).hom c)
      =
    (barycentricSubdivisionLinearMap R X n).hom
        ((singularBoundary R X n).hom c) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      (barycentricSubdivisionLinearMap_commutes_boundary R X n) c

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
