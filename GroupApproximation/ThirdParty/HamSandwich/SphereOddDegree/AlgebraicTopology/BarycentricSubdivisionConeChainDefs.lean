import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceOneZero
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainMap

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-! ## 7. The cone on chains -/

/-- The cone of a basis generator `[σ]`. -/
noncomputable def coneGenerator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  chainGenerator R (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)

/-- The `R`-linear map `R → C_{k+1}(Δⁿ; R)` sending `1` to `coneGenerator … σ`. -/
noncomputable def coneGeneratorHom (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  ModuleCat.ofHom
    { toFun := fun r => r • coneGenerator R n k v σ
      map_add' := by intro r s; simp [add_smul]
      map_smul' := by intro a r; simp [mul_smul] }

/-- **The cone operator on chains** `Cone_v : C_k(Δⁿ; R) → C_{k+1}(Δⁿ; R)`. -/
noncomputable def coneLinearMap (R : Type) [CommRing R] (n k : ℕ) (v : Delta n) :
    singularChainGroup R (TopCat.of (Delta n)) k
      ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  Sigma.desc fun σ : singularSimplices (TopCat.of (Delta n)) k => coneGeneratorHom R n k v σ

/-
The cone operator has the prescribed value on a basis generator.
-/
theorem coneLinearMap_generator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    (coneLinearMap R n k v).hom (chainGenerator R (TopCat.of (Delta n)) k σ)
      = coneGenerator R n k v σ := by
  convert one_smul _ _;
  convert congr_arg ( fun f : ModuleCat.of R R ⟶ singularChainGroup R { carrier := ( Delta n ), str := instTopologicalSpaceSubtype } ( k + 1 ) => f.hom 1 ) ( Sigma.ι_desc ( fun σ => coneGeneratorHom R n k v σ ) σ ) using 1
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

