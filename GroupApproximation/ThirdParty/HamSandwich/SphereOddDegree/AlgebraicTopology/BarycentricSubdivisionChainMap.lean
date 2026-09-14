/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricBoundaryChainMap
import Mathlib

/-!
# Barycentric subdivision as a chain map

This file packages the degree-wise barycentric subdivision maps
`barycentricSubdivisionLinearMap R X n` into a single morphism of chain
complexes from the singular chain complex of `X` to itself.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The singular chain complex `C_•(X; R)` of `X` with coefficients in `R`. -/
noncomputable abbrev singularChainComplex (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

/-- Barycentric subdivision as a chain map. -/
noncomputable def barycentricSubdivisionChainMap
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularChainComplex R X ⟶ singularChainComplex R X where
  f n := barycentricSubdivisionLinearMap R X n
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    exact barycentricSubdivisionLinearMap_commutes_boundary R X j

/-- Degree-wise component of the subdivision chain map. -/
@[simp] theorem barycentricSubdivisionChainMap_f_n
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMap R X).f n = barycentricSubdivisionLinearMap R X n :=
  rfl

/-- Generator formula for the subdivision chain map. -/
theorem barycentricSubdivisionChainMap_map_generator
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    ((barycentricSubdivisionChainMap R X).f n).hom (chainGenerator R X n σ)
      = barycentricSubdivisionGenerator R X n σ := by
  rw [barycentricSubdivisionChainMap_f_n, barycentricSubdivisionLinearMap_generator]

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
