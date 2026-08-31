import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV
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
open AffineBarycentricSubdivision

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

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
      ((singularChainComplex (ZMod 2) (TopCat.of (Sphere 0))).homology 0) = 2 := by
  have h_iso : (singularChainComplex (ZMod 2) (TopCat.of (Sphere 0))).homology 0 ≃ₗ[ZMod 2] DirectSum (Sphere 0) (fun _ => ZMod 2) := by
    convert ( singularHomologyFunctorZeroOfTotallyDisconnectedSpace ( ModuleCat ( ZMod 2 ) ) ( ModuleCat.of ( ZMod 2 ) ( ZMod 2 ) ) ( TopCat.of ( Sphere 0 ) ) ) |> CategoryTheory.Iso.toLinearEquiv |> LinearEquiv.trans <| ModuleCat.coprodIsoDirectSum _ |> CategoryTheory.Iso.toLinearEquiv;
  convert LinearEquiv.finrank_eq h_iso using 1;
  simp +decide [ Module.finrank ];
  rw [ show Cardinal.mk ( Sphere 0 ) = 2 from ?_ ] ; norm_num;
  obtain ⟨ e ⟩ := sphere0_equiv_fin2;
  simpa using Cardinal.mk_congr e

/-- The augmentation `H₀(Y; F₂) → F₂` is surjective for nonempty `Y`. -/
theorem H0aug_F2_surjective (Y : TopCat.{0}) [Nonempty Y] :
    Function.Surjective (H0Gen.H0aug (ZMod 2) Y).hom := by
  have h_surjective : Function.Surjective
      (⇑(ModuleCat.Hom.hom ((singularChainComplex (ZMod 2) Y).descOpcycles
        (H0Gen.aug (ZMod 2) Y) 1 H0Gen.prev_zero (H0Gen.aug_comp_boundary_eq_zero Y)))) := by
    intro n
    obtain ⟨b⟩ := ‹Nonempty Y›
    use (singularChainComplex (ZMod 2) Y).pOpcycles 0
      (n • chainGenerator (ZMod 2) Y 0 (pointSimplex Y b))
    convert congr_arg (fun f => f (n • chainGenerator (ZMod 2) Y 0 (pointSimplex Y b)))
      (HomologicalComplex.p_descOpcycles (singularChainComplex (ZMod 2) Y) (H0Gen.aug (ZMod 2) Y) 1
        H0Gen.prev_zero (by simp +decide [H0Gen.aug_comp_boundary_eq_zero])) using 1
    simp +decide
    erw [H0Gen.aug_generator]; aesop
  have hι : Function.Surjective
      ⇑(ModuleCat.Hom.hom ((singularChainComplex (ZMod 2) Y).homologyι 0)) := by
    haveI := H0Gen.isIso_homologyι_zero (R := ZMod 2) Y
    exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
  have : (H0Gen.H0aug (ZMod 2) Y).hom
      = (ModuleCat.Hom.hom ((singularChainComplex (ZMod 2) Y).descOpcycles
          (H0Gen.aug (ZMod 2) Y) 1 H0Gen.prev_zero (H0Gen.aug_comp_boundary_eq_zero Y))).comp
        (ModuleCat.Hom.hom ((singularChainComplex (ZMod 2) Y).homologyι 0)) := by
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
        ((singularChainComplex (ZMod 2) (TopCat.of (Sphere 0))).homology 0) :=
      Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
    have h := LinearMap.finrank_range_add_finrank_ker
      (H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0))).hom
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    simp only [finrank_top, Module.finrank_self] at h
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
  refine' ⟨ _ ⟩;
  have hnat : (homologyIsoOfHomotopyEquivModule (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) 0 (sphereBandHomotopyEquiv 0)).hom ≫ H0Gen.H0aug (ZMod 2) (TopCat.of (Sphere 0)) = H0Gen.H0aug (ZMod 2) (TopCat.of circBand) := by
    convert H0Gen.H0aug_natural _ using 1;
  refine' kernelIsIsoComp _ _ ≪≫ _;
  refine' kernelIsoOfEq hnat.symm ≪≫ _;
  refine' kernelIsIsoComp _ _ ≪≫ _;
  exact reducedH0_sphere0_iso_F2.some

/-- The mod-two MV left map's first component is the inclusion `U ∩ V ↪ U`. -/
theorem circF_comp_fst_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).f ≫ biprod.fst
      = mvInclUV_U (ZMod 2) circU circV := by
  convert biprod.lift_fst _ _ using 1

/-- The mod-two MV left map's second component is minus the inclusion `U ∩ V ↪ V`. -/
theorem circF_comp_snd_F2 :
    (mvShortComplex (ZMod 2) circU circV circUV_top).f ≫ biprod.snd
      = -(mvInclUV_V (ZMod 2) circU circV) := by
  convert biprod.lift_snd _ _

/-- **Joint monomorphism of the homology biproduct projections (F₂).** -/
theorem biprod_homology_zero_iff_F2
    (y : ((mvShortComplex (ZMod 2) circU circV circUV_top).X₂).homology 0) :
    y = 0 ↔
      (HomologicalComplex.homologyMap (biprod.fst :
          (subChainComplex (ZMod 2) circleTop ↑circU ⊞ subChainComplex (ZMod 2) circleTop ↑circV) ⟶ _) 0) y = 0
        ∧ (HomologicalComplex.homologyMap (biprod.snd :
          (subChainComplex (ZMod 2) circleTop ↑circU ⊞ subChainComplex (ZMod 2) circleTop ↑circV) ⟶ _) 0) y = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩
    have htot :
        (biprod.fst : (subChainComplex (ZMod 2) circleTop (circU : Set circleTop)
            ⊞ subChainComplex (ZMod 2) circleTop (circV : Set circleTop)) ⟶ _) ≫ biprod.inl
          + (biprod.snd : _ ⟶ _) ≫ biprod.inr
          = 𝟙 (subChainComplex (ZMod 2) circleTop (circU : Set circleTop)
            ⊞ subChainComplex (ZMod 2) circleTop (circV : Set circleTop)) := biprod.total
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
  refine' ⟨ _ ⟩;
  refine' ModuleCat.kernelIsoKer _ ≪≫ _ ≪≫ (ModuleCat.kernelIsoKer _).symm;
  refine' ( LinearEquiv.ofEq _ _ _ ).toModuleIso;
  refine' le_antisymm _ _ <;> intro x hx <;> simp_all +decide [ LinearMap.mem_ker ];
  · have hUx : ∀ z, (H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop))
        ((HomologicalComplex.homologyMap (mvInclUV_U (ZMod 2) circU circV) 0) z) = H0Gen.subH0aug (ZMod 2) circleTop circBand z := by
          intro z
          have h : (HomologicalComplex.homologyMap (mvInclUV_U (ZMod 2) circU circV) 0 ≫ H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop)) z = H0Gen.subH0aug (ZMod 2) circleTop circBand z := by
            convert congrArg ( fun ψ => ψ z ) ( H0Gen.subH0aug_natural_inclusion ( R := ZMod 2 ) circleTop circBand ( circU : Set circleTop ) Set.inter_subset_left ) using 1
          rw [CategoryTheory.comp_apply] at h
          exact h;
    have hfst : circF0_F2 ≫ HomologicalComplex.homologyMap (biprod.fst : (subChainComplex (ZMod 2) circleTop ↑circU ⊞ subChainComplex (ZMod 2) circleTop ↑circV) ⟶ _) 0
      = HomologicalComplex.homologyMap (mvInclUV_U (ZMod 2) circU circV) 0 := by
        rw [ ← circF_comp_fst_F2, HomologicalComplex.homologyMap_comp ];
    replace hfst := congr_arg ( fun f => f.hom x ) hfst ; simp_all +decide [ CategoryTheory.comp_apply ] ;
    rw [ ← hUx x, hfst.symm ] ; norm_num;
  · have hax : (HomologicalComplex.homologyMap (mvInclUV_U (ZMod 2) circU circV) 0) x = 0 := by
      have hUx : ∀ z, (H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop)).hom ((HomologicalComplex.homologyMap (mvInclUV_U (ZMod 2) circU circV) 0) z) = (H0Gen.subH0aug (ZMod 2) circleTop circBand).hom z := by
        intro z
        have hUeq : HomologicalComplex.homologyMap (mvInclUV_U (ZMod 2) circU circV) 0 ≫ H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop) = H0Gen.subH0aug (ZMod 2) circleTop circBand := by
          exact H0Gen.subH0aug_natural_inclusion _ _ _ _;
        exact congr_arg ( fun f => f z ) ( congr_arg ( fun f => f.hom ) hUeq );
      have hUx : Function.Injective (ModuleCat.Hom.hom (H0Gen.subH0aug (ZMod 2) circleTop (circU : Set circleTop))) := by
        have := H0Gen.isIso_subH0aug ( R := ZMod 2 ) circleTop ( circU : Set circleTop ) ; exact ( ModuleCat.mono_iff_injective _ ).mp inferInstance;
      exact hUx <| by aesop;
    have hbx : (HomologicalComplex.homologyMap (mvInclUV_V (ZMod 2) circU circV) 0) x = 0 := by
      have := H0Gen.subH0aug_natural_inclusion ( R := ZMod 2 ) circleTop circBand ( circV : Set circleTop ) Set.inter_subset_right;
      replace this := congr_arg ( fun f => f.hom x ) this; simp_all +decide [ CategoryTheory.comp_apply ] ;
      have := H0Gen.isIso_subH0aug ( R := ZMod 2 ) circleTop ( circV : Set circleTop ) ; exact (by
      obtain ⟨ f, hf ⟩ := this;
      replace hf := congr_arg ( fun g => g.hom ( ( ModuleCat.Hom.hom ( HomologicalComplex.homologyMap ( subChainInclusion circBand ↑circV Set.inter_subset_right ) 0 ) ) x ) ) hf.1; simp_all +decide [ CategoryTheory.comp_apply ] ;
      rw [ eq_comm ] at hf; aesop;);
    have hfx : (HomologicalComplex.homologyMap (biprod.fst : (subChainComplex (ZMod 2) circleTop ↑circU ⊞ subChainComplex (ZMod 2) circleTop ↑circV) ⟶ _) 0) (circF0_F2 x) = (HomologicalComplex.homologyMap (mvInclUV_U (ZMod 2) circU circV) 0) x := by
      rw [ ← circF_comp_fst_F2, HomologicalComplex.homologyMap_comp ];
      rfl;
    have hsx : (HomologicalComplex.homologyMap (biprod.snd : (subChainComplex (ZMod 2) circleTop ↑circU ⊞ subChainComplex (ZMod 2) circleTop ↑circV) ⟶ _) 0) (circF0_F2 x) = -((HomologicalComplex.homologyMap (mvInclUV_V (ZMod 2) circU circV) 0) x) := by
      have hsx : circF0_F2 ≫ HomologicalComplex.homologyMap (biprod.snd : (subChainComplex (ZMod 2) circleTop ↑circU ⊞ subChainComplex (ZMod 2) circleTop ↑circV) ⟶ _) 0 = -HomologicalComplex.homologyMap (mvInclUV_V (ZMod 2) circU circV) 0 := by
        convert congr_arg ( fun f => HomologicalComplex.homologyMap f 0 ) ( circF_comp_snd_F2 ) using 1;
        · rw [ HomologicalComplex.homologyMap_comp ];
        · exact Eq.symm (HomologicalComplex.homologyMap_neg (mvInclUV_V (ZMod 2) circU circV) 0);
      convert congr_arg ( fun f => f x ) hsx using 1;
    exact biprod_homology_zero_iff_F2 _ |>.2 ⟨ by aesop, by aesop ⟩

/-
`H₁(S¹; F₂) ≅ ker(H₀(U ∩ V; F₂) → H₀(U) ⊕ H₀(V))`, the connecting isomorphism
onto the Mayer–Vietoris kernel.
-/
theorem sphereH1_iso_kerF0_F2 :
    Nonempty (homologyZMod2 (TopCat.of (Sphere 1)) 1 ≅ kernel circF0_F2) := by
  refine' ⟨ _ ⟩;
  refine' ( smallChains_homologyIso ( ZMod 2 ) ( TopCat.of ( Sphere 1 ) ) ( twoSetCover circU circV circUV_top ) 1 ).symm.trans _;
  have hδ_mono : Mono ( (mvShortExact (ZMod 2) circU circV circUV_top).δ 1 0 (by simp [ComplexShape.down_Rel]) ) := by
    have hδ_mono : IsZero ( (mvShortComplex (ZMod 2) circU circV circUV_top).X₂.homology 1 ) := by
      apply isZero_mvX₂_homology;
      · convert isZero_subChainComplex_homologyZMod2_of_contractible circleTop ( upperOpens 0 ) 1 ( by norm_num ) using 1;
      · apply isZero_subChainComplex_homologyZMod2_of_contractible circleTop (lowerOpens 0) 1 (by norm_num);
    have := ( mvShortExact ( ZMod 2 ) circU circV circUV_top ).homology_exact₃ 1 0 ( by simp +decide [ ComplexShape.down_Rel ] );
    convert this.mono_g;
    simp +decide [ hδ_mono.eq_of_src ];
    exact Or.inl ( hδ_mono.eq_of_src _ _ );
  have := ( mvShortExact ( ZMod 2 ) circU circV circUV_top ).homology_exact₁ 1 0 ( by simp +decide [ ComplexShape.down_Rel ] );
  convert this.fIsKernel.conePointUniqueUpToIso ( kernelIsKernel circF0_F2 ) using 1

/-- **`H₁(S¹; F₂) ≅ F₂`.** -/
def sphereModTwo_one_iso' :
    homologyZMod2 (TopCat.of (Sphere 1)) 1 ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  (sphereH1_iso_kerF0_F2).some ≪≫ (kerF0_iso_kerBand_F2).some ≪≫ (kerBand_iso_F2).some

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
