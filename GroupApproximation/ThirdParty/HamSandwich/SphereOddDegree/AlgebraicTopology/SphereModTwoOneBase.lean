import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0General
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyVanishing
import Mathlib

/-!
# Mod-two Mayer–Vietoris base case: `H₁(S¹; F₂) ≅ F₂`

This mirrors the integral base computation `SphereHomologyS1BaseMV.lean`
(`sphereTopHomology_one_iso_nonempty : H₁(S¹; ℤ) ≅ ℤ`), but over the field `F₂`,
using the project's general-coefficient `H0Gen` augmentation machinery and the
general-coefficient subspace/small-chains homology isos.

The circle cover data `circleTop`, `circU`, `circV`, `circUV_top`, `circBand`
are reused from the integral base file (they are coefficient-independent).
-/

open CategoryTheory AlgebraicTopology Limits TopologicalSpace

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The singular chain complex with mod-two coefficients. -/
noncomputable abbrev singularChainComplexF2 (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).obj X

/-- The basis chain associated to a singular simplex, with mod-two coefficients. -/
noncomputable def chainGeneratorF2 (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X n) : (singularChainComplexF2 X).X n :=
  (Sigma.ι (fun _ : singularSimplices X n => ModuleCat.of (ZMod 2) (ZMod 2)) σ).hom 1

/-- The mod-two Mayer–Vietoris left map on `H₀`, `H₀(U ∩ V; F₂) → H₀(U; F₂) ⊕ H₀(V; F₂)`. -/
abbrev circF0_F2 :
    (subChainComplex (ZMod 2) circleTop circBand).homology 0 ⟶
      ((mvShortComplex (ZMod 2) circU circV circUV_top).X₂).homology 0 :=
  HomologicalComplex.homologyMap (mvShortComplex (ZMod 2) circU circV circUV_top).f 0

/-
`H₀(S⁰; F₂)` has `F₂`-dimension `2`.
-/
theorem h0_sphere0_F2_finrank :
    Module.finrank (ZMod 2)
      ((singularChainComplexF2 (TopCat.of (Sphere 0))).homology 0) = 2 := by
  obtain ⟨e⟩ := sphere0_equiv_fin2
  letI : Fintype (Sphere 0) := Fintype.ofEquiv (Fin 2) e.symm
  have hIso :
      (singularChainComplexF2 (TopCat.of (Sphere 0))).homology 0 ≅
        ModuleCat.of (ZMod 2) (DirectSum (Sphere 0) (fun _ => ZMod 2)) :=
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat (ZMod 2))
      (ModuleCat.of (ZMod 2) (ZMod 2)) (TopCat.of (Sphere 0)) ≪≫
        ModuleCat.coprodIsoDirectSum _
  let eFun : DirectSum (Sphere 0) (fun _ => ZMod 2) ≃ₗ[ZMod 2]
      (Sphere 0 → ZMod 2) := DFinsupp.linearEquivFunOnFintype
  rw [LinearEquiv.finrank_eq hIso.toLinearEquiv, LinearEquiv.finrank_eq eFun]
  simp [Fintype.card_congr e]

/-- The augmentation `H₀(Y; F₂) → F₂` is surjective for nonempty `Y`. -/
theorem H0aug_F2_surjective (Y : TopCat.{0}) [Nonempty Y] :
    Function.Surjective (H0Gen.H0aug (ZMod 2) Y).hom := by
  have h_surjective : Function.Surjective
      (⇑(ModuleCat.Hom.hom ((singularChainComplexF2 Y).descOpcycles
        (H0Gen.aug (ZMod 2) Y) 1 H0Gen.prev_zero (H0Gen.aug_comp_boundary_eq_zero Y)))) := by
    intro n
    obtain ⟨b⟩ := ‹Nonempty Y›
    use (singularChainComplexF2 Y).pOpcycles 0
      (n • chainGeneratorF2 Y 0 (pointSimplex Y b))
    have hp := HomologicalComplex.p_descOpcycles (singularChainComplexF2 Y)
      (H0Gen.aug (ZMod 2) Y) 1 H0Gen.prev_zero (H0Gen.aug_comp_boundary_eq_zero Y)
    calc
      _ = (H0Gen.aug (ZMod 2) Y).hom
          (n • chainGeneratorF2 Y 0 (pointSimplex Y b)) :=
        congrArg (fun g => g.hom (n • chainGeneratorF2 Y 0 (pointSimplex Y b))) hp
      _ = n := by
        rw [map_smul]
        have hgen : (H0Gen.aug (ZMod 2) Y).hom
            (chainGeneratorF2 Y 0 (pointSimplex Y b)) = 1 := by
          change (Limits.Sigma.desc (fun _ : singularSimplices Y 0 =>
              𝟙 (ModuleCat.of (ZMod 2) (ZMod 2)))).hom
            ((Limits.Sigma.ι (fun _ : singularSimplices Y 0 =>
              ModuleCat.of (ZMod 2) (ZMod 2)) (pointSimplex Y b)).hom 1) = 1
          rw [← ModuleCat.comp_apply, Limits.Sigma.ι_desc, ModuleCat.id_apply]
        rw [hgen, smul_eq_mul, mul_one]
  have hι : Function.Surjective
      ⇑(ModuleCat.Hom.hom ((singularChainComplexF2 Y).homologyι 0)) := by
    haveI := H0Gen.isIso_homologyι_zero (R := ZMod 2) Y
    exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
  have : (H0Gen.H0aug (ZMod 2) Y).hom
      = (ModuleCat.Hom.hom ((singularChainComplexF2 Y).descOpcycles
          (H0Gen.aug (ZMod 2) Y) 1 H0Gen.prev_zero (H0Gen.aug_comp_boundary_eq_zero Y))).comp
        (ModuleCat.Hom.hom ((singularChainComplexF2 Y).homologyι 0)) := by
    rfl
  rw [this]
  exact h_surjective.comp hι

/-- **Reduced zeroth mod-two homology of `S⁰`.** The kernel of the augmentation
`H₀(S⁰; F₂) → F₂` is isomorphic to `F₂`. -/
theorem reducedH0_sphere0_iso_F2 :
    Nonempty (kernel (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0)))
      ≅ ModuleCat.of (ZMod 2) (ZMod 2)) := by
  have hsurj := H0aug_F2_surjective (TopCat.of (Sphere 0))
  have hrank := h0_sphere0_F2_finrank
  -- kernel has finrank 1 by rank-nullity
  have hker : Module.finrank (ZMod 2)
      (LinearMap.ker (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))).hom) = 1 := by
    have hfin : Module.Finite (ZMod 2)
        ((singularChainComplexF2 (TopCat.of (Sphere 0))).homology 0) :=
      Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
    have h := LinearMap.finrank_range_add_finrank_ker
      (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))).hom
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    simp only [finrank_top, Module.finrank_self] at h
    rw [hrank] at h
    omega
  -- a finrank-1 F₂-space is LinearEquiv to F₂
  have hfinK : Module.Finite (ZMod 2)
      (LinearMap.ker (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))).hom) :=
    Module.finite_of_finrank_pos (by rw [hker]; norm_num)
  obtain ⟨e⟩ : Nonempty (LinearMap.ker (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))).hom
      ≃ₗ[ZMod 2] ZMod 2) :=
    ⟨LinearEquiv.ofFinrankEq _ _ (by rw [hker, Module.finrank_self])⟩
  exact ⟨ModuleCat.kernelIsoKer _ ≪≫ e.toModuleIso⟩

/-
The kernel of the mod-two band augmentation `H₀(U ∩ V; F₂) → F₂` is
isomorphic to `F₂`, using the homotopy equivalence `U ∩ V ≃ S⁰`.
-/
theorem kerBand_iso_F2 :
    Nonempty (kernel (H0Gen.subH0aug (ZMod 2) circleTop circBand)
      ≅ ModuleCat.of (ZMod 2) (ZMod 2)) := by
  have hnat :
      (homologyIsoOfHomotopyEquivModule (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))
        0 (sphereBandHomotopyEquiv 0)).hom ≫
          H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0)) =
        H0Gen.H0aug (ZMod 2) (TopCat.of circBand) :=
    H0Gen.H0aug_natural (TopCat.ofHom (sphereBandHomotopyEquiv 0).toFun)
  let iSub : kernel (H0Gen.subH0aug (ZMod 2) circleTop circBand) ≅
      kernel (H0Gen.H0aug (ZMod 2) (TopCat.of circBand)) :=
    kernelIsIsoComp
      (subspaceHomologyIso (R := ZMod 2) (X := circleTop) circBand 0).hom
      (H0Gen.H0aug (ZMod 2) (TopCat.of circBand))
  let iNat : kernel (H0Gen.H0aug (ZMod 2) (TopCat.of circBand)) ≅
      kernel ((homologyIsoOfHomotopyEquivModule (ZMod 2)
        (ModuleCat.of (ZMod 2) (ZMod 2)) 0 (sphereBandHomotopyEquiv 0)).hom ≫
          H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))) :=
    kernelIsoOfEq hnat.symm
  let iSphere : kernel ((homologyIsoOfHomotopyEquivModule (ZMod 2)
      (ModuleCat.of (ZMod 2) (ZMod 2)) 0 (sphereBandHomotopyEquiv 0)).hom ≫
        H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))) ≅
      kernel (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))) :=
    kernelIsIsoComp
      (homologyIsoOfHomotopyEquivModule (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))
        0 (sphereBandHomotopyEquiv 0)).hom
      (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0)))
  exact ⟨iSub ≪≫ iNat ≪≫ iSphere ≪≫ reducedH0_sphere0_iso_F2.some⟩

/-- The first biproduct projection from the mod-two Mayer--Vietoris middle term. -/
abbrev circProjU_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).X₂ ⟶
      subChainComplex (ZMod 2) circleTop (circU : Set circleTop) :=
  biprod.fst

/-- The second biproduct projection from the mod-two Mayer--Vietoris middle term. -/
abbrev circProjV_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).X₂ ⟶
      subChainComplex (ZMod 2) circleTop (circV : Set circleTop) :=
  biprod.snd

/-- The first injection into the mod-two Mayer--Vietoris middle term. -/
abbrev circInU_F2 :
    subChainComplex (ZMod 2) circleTop (circU : Set circleTop) ⟶
      (mvShortComplex (ZMod 2) circU circV circUV_top).X₂ :=
  biprod.inl

/-- The second injection into the mod-two Mayer--Vietoris middle term. -/
abbrev circInV_F2 :
    subChainComplex (ZMod 2) circleTop (circV : Set circleTop) ⟶
      (mvShortComplex (ZMod 2) circU circV circUV_top).X₂ :=
  biprod.inr

/-- The band inclusion into the upper cover member, with its source fixed. -/
abbrev circInclU_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).X₁ ⟶
      subChainComplex (ZMod 2) circleTop (circU : Set circleTop) :=
  mvInclUV_U (ZMod 2) circU circV

/-- The band inclusion into the lower cover member, with its source fixed. -/
abbrev circInclV_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).X₁ ⟶
      subChainComplex (ZMod 2) circleTop (circV : Set circleTop) :=
  mvInclUV_V (ZMod 2) circU circV

/-- The mod-two MV left map's first component is the inclusion `U ∩ V ↪ U`. -/
theorem circF_comp_fst_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).f ≫ circProjU_F2
      = circInclU_F2 := by
  exact biprod.lift_fst _ _

/-- The mod-two MV left map's second component is minus the inclusion `U ∩ V ↪ V`. -/
theorem circF_comp_snd_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).f ≫ circProjV_F2
      = -circInclV_F2 := by
  exact biprod.lift_snd _ _

/-- **Joint monomorphism of the homology biproduct projections (F₂).** -/
theorem biprod_homology_zero_iff_F2
    (y : ((mvShortComplex (ZMod 2) circU circV circUV_top).X₂).homology 0) :
    y = 0 ↔
      (HomologicalComplex.homologyMap circProjU_F2 0) y = 0 ∧
        (HomologicalComplex.homologyMap circProjV_F2 0) y = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩
  · rintro ⟨h1, h2⟩
    have htot :
        circProjU_F2 ≫ circInU_F2 + circProjV_F2 ≫ circInV_F2 =
          𝟙 (mvShortComplex (ZMod 2) circU circV circUV_top).X₂ := biprod.total
    have hmap := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) htot
    simp only [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_id] at hmap
    have hy := congrArg (fun ψ => ψ y) hmap
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, h1, h2,
      map_zero, add_zero] at hy
    exact hy.symm

/-
**The mod-two Mayer–Vietoris kernel coincides with the reduced-`H₀` kernel.**
`ker(H₀(U ∩ V; F₂) → H₀(U) ⊕ H₀(V)) ≅ ker(H₀(U ∩ V; F₂) → F₂)`.
-/
theorem kerF0_iso_kerBand_F2 :
    Nonempty (kernel circF0_F2 ≅ kernel (H0Gen.subH0aug (ZMod 2) circleTop circBand)) := by
  haveI := H0Gen.isIso_subH0aug (R := ZMod 2) circleTop (circU : Set circleTop)
  haveI := H0Gen.isIso_subH0aug (R := ZMod 2) circleTop (circV : Set circleTop)
  have hUeq : HomologicalComplex.homologyMap circInclU_F2 0 ≫
      H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop) =
        H0Gen.subH0aug (ZMod 2) circleTop circBand :=
    H0Gen.subH0aug_natural_inclusion circleTop circBand
      (circU : Set circleTop) Set.inter_subset_left
  have hVeq : HomologicalComplex.homologyMap circInclV_F2 0 ≫
      H0Gen.subH0aug (ZMod 2) circleTop (circV : Set circleTop) =
        H0Gen.subH0aug (ZMod 2) circleTop circBand :=
    H0Gen.subH0aug_natural_inclusion circleTop circBand
      (circV : Set circleTop) Set.inter_subset_right
  have hfst : circF0_F2 ≫ HomologicalComplex.homologyMap circProjU_F2 0 =
      HomologicalComplex.homologyMap circInclU_F2 0 := by
    have hm := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) circF_comp_fst_F2
    rw [HomologicalComplex.homologyMap_comp] at hm
    exact hm
  have hsnd : circF0_F2 ≫ HomologicalComplex.homologyMap circProjV_F2 0 =
      -(HomologicalComplex.homologyMap circInclV_F2 0) := by
    have hm := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) circF_comp_snd_F2
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg] at hm
    exact hm
  have hinjU : Function.Injective
      (ModuleCat.Hom.hom (H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hinjV : Function.Injective
      (ModuleCat.Hom.hom (H0Gen.subH0aug (ZMod 2) circleTop (circV : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hUx : ∀ z, H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop)
      ((HomologicalComplex.homologyMap circInclU_F2 0) z) =
        H0Gen.subH0aug (ZMod 2) circleTop circBand z := by
    intro z
    have h := congrArg (fun ψ => ψ z) hUeq
    rwa [CategoryTheory.comp_apply] at h
  have hVx : ∀ z, H0Gen.subH0aug (ZMod 2) circleTop (circV : Set circleTop)
      ((HomologicalComplex.homologyMap circInclV_F2 0) z) =
        H0Gen.subH0aug (ZMod 2) circleTop circBand z := by
    intro z
    have h := congrArg (fun ψ => ψ z) hVeq
    rwa [CategoryTheory.comp_apply] at h
  have hfx : ∀ z, (HomologicalComplex.homologyMap circProjU_F2 0) (circF0_F2 z) =
      (HomologicalComplex.homologyMap circInclU_F2 0) z := by
    intro z
    have h := congrArg (fun ψ => ψ z) hfst
    rwa [CategoryTheory.comp_apply] at h
  have hsx : ∀ z, (HomologicalComplex.homologyMap circProjV_F2 0) (circF0_F2 z) =
      -((HomologicalComplex.homologyMap circInclV_F2 0) z) := by
    intro z
    have h := congrArg (fun ψ => ψ z) hsnd
    rw [CategoryTheory.comp_apply] at h
    change _ = (-(HomologicalComplex.homologyMap circInclV_F2 0)) z
    exact h
  have hker : LinearMap.ker (ModuleCat.Hom.hom circF0_F2) =
      LinearMap.ker (ModuleCat.Hom.hom
        (H0Gen.subH0aug (ZMod 2) circleTop circBand)) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← hUx x, ← hfx x, hx, map_zero, map_zero]
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hax : (HomologicalComplex.homologyMap circInclU_F2 0) x = 0 := by
        apply hinjU
        rw [map_zero, hUx x, hx]
      have hbx : (HomologicalComplex.homologyMap circInclV_F2 0) x = 0 := by
        apply hinjV
        rw [map_zero, hVx x, hx]
      refine (biprod_homology_zero_iff_F2 (circF0_F2 x)).mpr ⟨?_, ?_⟩
      · rw [hfx x, hax]
      · rw [hsx x, hbx, neg_zero]
  exact ⟨ModuleCat.kernelIsoKer circF0_F2 ≪≫ eqToIso (by rw [hker]) ≪≫
    (ModuleCat.kernelIsoKer (H0Gen.subH0aug (ZMod 2) circleTop circBand)).symm⟩

/-
`H₁(S¹; F₂) ≅ ker(H₀(U ∩ V; F₂) → H₀(U) ⊕ H₀(V))`, the connecting isomorphism
onto the Mayer–Vietoris kernel.
-/
theorem sphereH1_iso_kerF0_F2 :
    Nonempty (homologyZMod2 (TopCat.of (Sphere 1)) 1 ≅ kernel circF0_F2) := by
  have hδ_mono : Mono
      ((mvShortExact (ZMod 2) circU circV circUV_top).δ 1 0
        (by simp [ComplexShape.down_Rel])) := by
    have hzero : IsZero
        ((mvShortComplex (ZMod 2) circU circV circUV_top).X₂.homology 1) := by
      apply isZero_mvX₂_homology
      · convert isZero_subChainComplex_homologyZMod2_of_contractible
          circleTop (circU : Set circleTop) 1 (by norm_num) using 1
      · exact isZero_subChainComplex_homologyZMod2_of_contractible
          circleTop (circV : Set circleTop) 1 (by norm_num)
    have hex := (mvShortExact (ZMod 2) circU circV circUV_top).homology_exact₃
      1 0 (by simp [ComplexShape.down_Rel])
    exact hex.mono_g (hzero.eq_of_src _ _)
  have hex := (mvShortExact (ZMod 2) circU circV circUV_top).homology_exact₁
    1 0 (by simp [ComplexShape.down_Rel])
  exact ⟨(smallChains_homologyIso (ZMod 2) (TopCat.of (Sphere 1))
      (twoSetCover circU circV circUV_top) 1).symm ≪≫
    hex.fIsKernel.conePointUniqueUpToIso (limit.isLimit (parallelPair circF0_F2 0))⟩

/-- **`H₁(S¹; F₂) ≅ F₂`.** -/
def sphereModTwo_one_iso' :
    homologyZMod2 (TopCat.of (Sphere 1)) 1 ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  (sphereH1_iso_kerF0_F2).some ≪≫ (kerF0_iso_kerBand_F2).some ≪≫ (kerBand_iso_F2).some

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
