import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SmallChainComplex
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.IteratedSubdivisionSmallChains
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionIter

/-!
# The small-chain inclusion is surjective on homology

For an open cover `𝒰` of a space `X`, this file proves that the inclusion chain
map `smallChainsInclusion R X 𝒰 : C_*^𝒰(X; R) ⟶ C_*(X; R)` of small singular
chains into all singular chains induces a **surjection on homology** in every
degree.

## Mathematical proof

Let `[z] ∈ Hₙ(C_*(X))` be a homology class, represented by a cycle `z` (`∂z = 0`).
By `exists_iteratedSubdivision_chain_mem_smallChains`, choose `N` with `sdᴺ z` a
small chain.  Since `sd` is a chain map, `sdᴺ z` is still a cycle, hence defines a
class in the small-chain homology.  Since `sdᴺ` is chain-homotopic to the identity
(`barycentricSubdivisionIter_induces_identity_on_homology`), `[sdᴺ z] = [z]` in the
full homology.  As `sdᴺ z = ι(sdᴺ z)` is the image of a small cycle, the class
`[z]` lies in the image of the inclusion on homology.

## Main results

* `SphereOddDegree.homologyMapInDegree` — the degree-`n` induced map on homology,
  packaged as a function.
* `SphereOddDegree.smallChainsInclusion_surjective_on_homology` — the inclusion of
  small chains is surjective on homology in every degree.
-/

open CategoryTheory AlgebraicTopology
open AffineBarycentricSubdivision

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The induced map on degree-`n` homology of a chain map, packaged as a
function on the underlying homology modules. -/
noncomputable def homologyMapInDegree {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (n : ℕ) : K.homology n → L.homology n :=
  ⇑(HomologicalComplex.homologyMap f n).hom

theorem homologyMapInDegree_apply {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (n : ℕ) (x : K.homology n) :
    homologyMapInDegree f n x = (HomologicalComplex.homologyMap f n).hom x :=
  rfl

/-- Every degree-`n` homology class of a `ModuleCat`-valued chain complex is the
image of a cycle under the homology projection `homologyπ`. -/
theorem homologyπ_surjective (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Surjective (K.homologyπ n).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

/-- **The inclusion of small chains is surjective on homology** in every degree. -/
theorem smallChainsInclusion_surjective_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    Function.Surjective (homologyMapInDegree (smallChainsInclusion R X 𝒰) n) := by
  intro y
  -- Lift `y` to a cycle `z` in the full singular complex.
  obtain ⟨z, hz⟩ := homologyπ_surjective (singularChainComplex R X) n y
  -- The underlying singular chain of `z`, and its cycle condition `∂c = 0`.
  set c := ((singularChainComplex R X).iCycles n).hom z with hcdef
  have hcyc : ((singularChainComplex R X).d n ((ComplexShape.down ℕ).next n)).hom c = 0 := by
    have h := HomologicalComplex.iCycles_d (singularChainComplex R X) n
      ((ComplexShape.down ℕ).next n)
    have h2 := congrArg (fun m => m.hom z) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h2
    exact h2
  -- Choose `N` such that `sdᴺ c` is a small chain.
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_chain_mem_smallChains 𝒰 R n c
  -- The small chain `cS = sdᴺ c`, as an element of the small-chain submodule.
  set cS : smallChainSubmodule R X 𝒰 n :=
    ⟨barycentricSubdivisionIterLinearMap R X N n c, hN⟩ with hcS
  -- `cS` is a cycle in the small complex.
  have hcond : (ConcreteCategory.hom ((forget₂ (ModuleCat.{0} R) Ab).map
      ((smallChainComplex R X 𝒰).d n ((ComplexShape.down ℕ).next n)))) cS = 0 := by
    show ((smallChainComplex R X 𝒰).d n ((ComplexShape.down ℕ).next n)).hom cS = 0
    have hinj : Function.Injective
        ((smallChainsInclusion R X 𝒰).f ((ComplexShape.down ℕ).next n)).hom := by
      intro a b hab
      apply Subtype.ext
      rw [smallChainsInclusion_f_apply, smallChainsInclusion_f_apply] at hab
      exact hab
    apply hinj
    rw [map_zero]
    have hcomm := (smallChainsInclusion R X 𝒰).comm n ((ComplexShape.down ℕ).next n)
    have hcomm2 := congrArg (fun m => m.hom cS) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm2
    rw [← hcomm2]
    have hiota : ((smallChainsInclusion R X 𝒰).f n).hom cS
        = barycentricSubdivisionIterLinearMap R X N n c := by
      rw [smallChainsInclusion_f_apply]
    rw [hiota]
    -- `(∂ ∘ sdᴺ) c = (sdᴺ ∘ ∂) c = sdᴺ 0 = 0`.
    have hsdc : barycentricSubdivisionIterLinearMap R X N n c
        = ((barycentricSubdivisionIterChainMap R X N).f n).hom c := rfl
    rw [hsdc]
    have hsd := (barycentricSubdivisionIterChainMap R X N).comm n
      ((ComplexShape.down ℕ).next n)
    have hsd2 := congrArg (fun m => m.hom c) hsd
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsd2
    rw [hsd2, hcyc, map_zero]
  -- The small cycle.
  set zSmall := (smallChainComplex R X 𝒰).cyclesMk cS ((ComplexShape.down ℕ).next n) rfl hcond
    with hzSmall
  refine ⟨((smallChainComplex R X 𝒰).homologyπ n).hom zSmall, ?_⟩
  rw [homologyMapInDegree_apply]
  -- Naturality of `homologyπ` for the inclusion.
  have hnat := HomologicalComplex.homologyπ_naturality (smallChainsInclusion R X 𝒰) n
  have hnat2 := congrArg (fun m => m.hom zSmall) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat2
  rw [hnat2]
  -- The image cycle `cyclesMap ι zSmall` equals `cyclesMap sdᴺ z` (both have
  -- underlying chain `sdᴺ c`); use that `iCycles` is mono (injective).
  have hcyceq : (HomologicalComplex.cyclesMap (smallChainsInclusion R X 𝒰) n).hom zSmall
      = (HomologicalComplex.cyclesMap (barycentricSubdivisionIterChainMap R X N) n).hom z := by
    apply (ModuleCat.mono_iff_injective ((singularChainComplex R X).iCycles n)).mp inferInstance
    have hL := HomologicalComplex.cyclesMap_i (smallChainsInclusion R X 𝒰) n
    have hL2 := congrArg (fun m => m.hom zSmall) hL
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hL2
    have hR := HomologicalComplex.cyclesMap_i (barycentricSubdivisionIterChainMap R X N) n
    have hR2 := congrArg (fun m => m.hom z) hR
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hR2
    rw [hL2, hR2]
    have hik : ((smallChainComplex R X 𝒰).iCycles n).hom zSmall = cS := by
      have := HomologicalComplex.i_cyclesMk (smallChainComplex R X 𝒰) cS
        ((ComplexShape.down ℕ).next n) rfl hcond
      exact this
    rw [hik, smallChainsInclusion_f_apply]
    rfl
  rw [hcyceq]
  -- Naturality of `homologyπ` for `sdᴺ`, then `sdᴺ = id` on homology.
  have hnatsd := HomologicalComplex.homologyπ_naturality
    (barycentricSubdivisionIterChainMap R X N) n
  have hnatsd2 := congrArg (fun m => m.hom z) hnatsd
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnatsd2
  rw [← hnatsd2, hz, barycentricSubdivisionIter_induces_identity_on_homology]
  simp

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
