import GroupApproximation.CharClass.KroneckerClassifier
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyVanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0General
import GroupApproximation.Meta.AxiomGuard

/-!
# The singular homology of a sphere, over any coefficient field

Step 4b of the universal-coefficient port (lane `lix-cupone`, successor of `sp-cupone`):
the homology half of the sphere computation, over `K`.

```text
Hₖ(Sⁿ; K) = 0   for k ∉ {0, n},        Hₙ(Sⁿ; K) ≅ K   for n ≥ 1.
```

The vendored `ThirdParty/.../SphereModTwoHomologyVanishing.lean`,
`SphereModTwoHomologyAboveDimension.lean`, `SphereModTwoOneBase.lean` and
`SphereModTwoTopClass.lean` prove exactly this at `K = ZMod 2`.  Every `ZMod 2` in them is
an instantiation of an already coefficient-generic construction — `subChainComplex R`,
`mvShortComplex R`, `mvHomologyIso_succ R`, `homologyIsoOfHomotopyEquivModule R`,
`H0Gen.H0aug R` — so this file is substitution, and nothing vendored is edited.

`[CommRing K]` suffices for the vanishing range and the suspension isomorphism.  `[Field K]`
enters only at the base case `H₁(S¹; K) ≅ K`, through a rank count: the reduced `H₀(S⁰; K)`
is the kernel of a surjection from a two-dimensional space onto `K`.

The cohomology statements, which dualise these through `kroneckerEquivOf`, are
`KroneckerSphere.lean`.
-/

open CategoryTheory AlgebraicTopology Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

noncomputable section

namespace GroupApproximation
namespace CharClass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Contractible pieces, and the suspension isomorphism -/

/-- **Positive homology of a contractible subspace vanishes, over any `K`.** -/
theorem isZero_subChainComplex_homologyOf_of_contractible (K : Type) [CommRing K]
    (X : TopCat.{0}) (S : Set X) [ContractibleSpace S] (m : ℕ) (hm : 1 ≤ m) :
    IsZero ((subChainComplex K X S).homology m) := by
  obtain ⟨e⟩ := ‹ContractibleSpace S›
  obtain ⟨e⟩ := e
  have hUnit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat K) m (ModuleCat.of K K) (TopCat.of Unit) (by omega)
  change IsZero (homologyOf K (TopCat.of Unit) m) at hUnit
  exact IsZero.of_iso hUnit
    (subspaceHomologyIso S m ≪≫ homologyIsoOfHomotopyEquivModule K (ModuleCat.of K K) m e)

/-- **The suspension isomorphism over `K`.**  For `j ≥ 1`,
`H_{j+1}(Sⁿ⁺¹; K) ≅ H_j(Sⁿ; K)`. -/
def sphereSuspensionOf (K : Type) [CommRing K] (n j : ℕ) (hj : 1 ≤ j) :
    homologyOf K (TopCat.of (Sphere (n + 1))) (j + 1) ≅
      homologyOf K (TopCat.of (Sphere n)) j :=
  (mvHomologyIso_succ K (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) j
      (isZero_subChainComplex_homologyOf_of_contractible K _ _ (j + 1) (by omega))
      (isZero_subChainComplex_homologyOf_of_contractible K _ _ (j + 1) (by omega))
      (isZero_subChainComplex_homologyOf_of_contractible K _ _ j hj)
      (isZero_subChainComplex_homologyOf_of_contractible K _ _ j hj))
    ≪≫ subspaceHomologyIso _ j
    ≪≫ homologyIsoOfHomotopyEquivModule K (ModuleCat.of K K) j (sphereBandHomotopyEquiv n)

/-! ## 2. Vanishing above the dimension -/

/-- **`Hₖ(Sⁿ; K) = 0` for `n < k`.**  Induction on `n`: `S⁰` is totally disconnected, and the
suspension isomorphism raises both indices. -/
theorem sphereHomologyOf_isZero_of_gt (K : Type) [CommRing K] (n k : ℕ) (hnk : n < k) :
    IsZero (homologyOf K (TopCat.of (Sphere n)) k) := by
  induction n generalizing k with
  | zero =>
    have hzero :=
      AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat K) k (ModuleCat.of K K) (TopCat.of (Sphere 0)) (by omega)
    change IsZero (homologyOf K (TopCat.of (Sphere 0)) k) at hzero
    exact hzero
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact IsZero.of_iso (ih j (by omega)) (sphereSuspensionOf K m j (by omega))

/-! ## 3. Vanishing in the middle range -/

/-- The Mayer–Vietoris left map on `H₀` of the sphere cover, over `K`. -/
abbrev mvF0Of (K : Type) [CommRing K] (m : ℕ) :
    (subChainComplex K (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m))
          ∩ (lowerOpens m : Set (sphereSpace m)))).homology 0 ⟶
      ((mvShortComplex K (upperOpens m) (lowerOpens m)
          (upperOpens_sup_lowerOpens m)).X₂).homology 0 :=
  HomologicalComplex.homologyMap
    (mvShortComplex K (upperOpens m) (lowerOpens m) (upperOpens_sup_lowerOpens m)).f 0

/-- **The Mayer–Vietoris `H₀` map is injective** for `m ≥ 1`: the band is path connected, so
its augmentation is an isomorphism, and the augmentation factors through the upper piece. -/
theorem mvF0Of_injective (K : Type) [CommRing K] (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (mvF0Of K m).hom := by
  let projU := HomologicalComplex.homologyMap
    (biprod.fst :
      (subChainComplex K (sphereSpace m) (upperOpens m) ⊞
        subChainComplex K (sphereSpace m) (lowerOpens m)) ⟶ _) 0
  let inclU := HomologicalComplex.homologyMap
    (mvInclUV_U K (upperOpens m) (lowerOpens m)) 0
  have h_mvF0 : mvF0Of K m ≫ projU = inclU := by
    have hchain :
        (mvShortComplex K (upperOpens m) (lowerOpens m)
            (upperOpens_sup_lowerOpens m)).f ≫
            (biprod.fst :
              (subChainComplex K (sphereSpace m) (upperOpens m) ⊞
                subChainComplex K (sphereSpace m) (lowerOpens m)) ⟶ _)
          = mvInclUV_U K (upperOpens m) (lowerOpens m) :=
      biprod.lift_fst _ _
    have := congrArg (fun f => HomologicalComplex.homologyMap f 0) hchain
    simpa only [mvF0Of, projU, inclU, HomologicalComplex.homologyMap_comp] using this
  have h_mvInclUV_U : inclU ≫
      H0Gen.subH0aug K (sphereSpace m) (upperOpens m : Set (sphereSpace m)) =
      H0Gen.subH0aug K (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m))) := by
    simpa only [inclU, mvInclUV_U] using
      H0Gen.subH0aug_natural_inclusion (R := K) (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m)))
        (upperOpens m : Set (sphereSpace m)) Set.inter_subset_left
  haveI : PathConnectedSpace
      ↥((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m))) :=
    sphereBand_pathConnected m hm
  have h_aug_inj : Function.Injective
      (H0Gen.subH0aug K (sphereSpace m)
        ((upperOpens m : Set (sphereSpace m)) ∩ (lowerOpens m : Set (sphereSpace m)))).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  intro x y hxy
  apply h_aug_inj
  have hproj : projU.hom ((mvF0Of K m).hom x) = projU.hom ((mvF0Of K m).hom y) :=
    congrArg projU.hom hxy
  have hincl : inclU.hom x = inclU.hom y := by
    have hx := congrArg (fun f => f.hom x) h_mvF0
    have hy := congrArg (fun f => f.hom y) h_mvF0
    simp only [CategoryTheory.comp_apply] at hx hy
    exact hx.symm.trans (hproj.trans hy)
  have hupper := congrArg
    (H0Gen.subH0aug K (sphereSpace m)
      (upperOpens m : Set (sphereSpace m))).hom hincl
  have hx := congrArg (fun f => f.hom x) h_mvInclUV_U
  have hy := congrArg (fun f => f.hom y) h_mvInclUV_U
  simp only [CategoryTheory.comp_apply] at hx hy
  exact hx.symm.trans (hupper.trans hy)

/-- The small-chains `H₁` of the sphere cover vanishes for `m ≥ 1`: the connecting map into
`H₀` of the band is injective, and its range is the kernel of the injective `mvF0Of`. -/
theorem mvX3_H1_isZeroOf (K : Type) [CommRing K] (m : ℕ) (hm : 1 ≤ m) :
    IsZero ((mvShortComplex K (upperOpens m) (lowerOpens m)
        (upperOpens_sup_lowerOpens m)).X₃.homology 1) := by
  let S := mvShortComplex K (upperOpens m) (lowerOpens m)
    (upperOpens_sup_lowerOpens m)
  let hS := mvShortExact K (upperOpens m) (lowerOpens m)
    (upperOpens_sup_lowerOpens m)
  let δ := hS.δ 1 0 rfl
  have hX2 : IsZero (S.X₂.homology 1) :=
    isZero_mvX₂_homology K (upperOpens m) (lowerOpens m)
      (upperOpens_sup_lowerOpens m) 1
      (isZero_subChainComplex_homologyOf_of_contractible K (sphereSpace m)
        (upperOpens m : Set (sphereSpace m)) 1 (by norm_num))
      (isZero_subChainComplex_homologyOf_of_contractible K (sphereSpace m)
        (lowerOpens m : Set (sphereSpace m)) 1 (by norm_num))
  haveI : Mono δ := hS.homology_exact₃ 1 0 rfl |>.mono_g (hX2.eq_of_src _ _)
  have hδ_inj : Function.Injective δ.hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hzero : ∀ x : S.X₃.homology 1, x = 0 := by
    intro x
    apply hδ_inj
    rw [map_zero]
    apply mvF0Of_injective K m hm
    have hmem : δ.hom x ∈ LinearMap.ker (mvF0Of K m).hom := by
      rw [← hS.homology_exact₁ 1 0 rfl |>.moduleCat_range_eq_ker]
      exact LinearMap.mem_range_self δ.hom x
    exact (LinearMap.mem_ker.mp hmem).trans (map_zero (mvF0Of K m).hom).symm
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- **`H₁(Sⁿ; K) = 0` for `n ≥ 2`.** -/
theorem sphereH1Of_isZero (K : Type) [CommRing K] (n : ℕ) (hn : 2 ≤ n) :
    IsZero (homologyOf K (TopCat.of (Sphere n)) 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  refine IsZero.of_iso (mvX3_H1_isZeroOf K m hm) ?_
  exact (smallChains_homologyIso K (TopCat.of (Sphere (m + 1)))
    (twoSetCover (upperOpens m) (lowerOpens m) (upperOpens_sup_lowerOpens m)) 1).symm

/-- **`Hₖ(Sⁿ; K) = 0` for `0 < k < n`.** -/
theorem sphereHomologyOf_isZero_of_lt (K : Type) [CommRing K] (n k : ℕ) (h0 : 0 < k)
    (hkn : k < n) : IsZero (homologyOf K (TopCat.of (Sphere n)) k) := by
  induction n generalizing k with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      exact sphereH1Of_isZero K (m + 1) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact IsZero.of_iso (ih j (by omega) (by omega)) (sphereSuspensionOf K m j (by omega))

/-- **`Hₖ(Sⁿ; K) = 0` whenever `k ∉ {0, n}`.** -/
theorem sphereHomologyOf_isZero_of_ne (K : Type) [CommRing K] (n k : ℕ) (h0 : k ≠ 0)
    (hkn : k ≠ n) : IsZero (homologyOf K (TopCat.of (Sphere n)) k) := by
  rcases lt_or_gt_of_ne hkn with h | h
  · exact sphereHomologyOf_isZero_of_lt K n k (Nat.pos_of_ne_zero h0) h
  · exact sphereHomologyOf_isZero_of_gt K n k h

/-! ## 4. The base case `H₁(S¹; K) ≅ K` -/

/-- `H₀(S⁰; K)` has dimension `2`: `S⁰` is totally disconnected with two points. -/
theorem h0_sphere0Of_finrank (K : Type) [Field K] :
    Module.finrank K (homologyOf K (TopCat.of (Sphere 0)) 0) = 2 := by
  obtain ⟨e⟩ := sphere0_equiv_fin2
  letI : Fintype (Sphere 0) := Fintype.ofEquiv (Fin 2) e.symm
  have hIso :
      homologyOf K (TopCat.of (Sphere 0)) 0 ≅
        ModuleCat.of K (DirectSum (Sphere 0) (fun _ => K)) :=
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat K)
      (ModuleCat.of K K) (TopCat.of (Sphere 0)) ≪≫
        ModuleCat.coprodIsoDirectSum _
  let eFun : DirectSum (Sphere 0) (fun _ => K) ≃ₗ[K] (Sphere 0 → K) :=
    DFinsupp.linearEquivFunOnFintype
  rw [LinearEquiv.finrank_eq hIso.toLinearEquiv, LinearEquiv.finrank_eq eFun]
  simp [Fintype.card_congr e]

/-- The augmentation `H₀(Y; K) → K` is surjective for nonempty `Y`: a point simplex
carrying `r` augments to `r`. -/
theorem H0augOf_surjective (K : Type) [CommRing K] (Y : TopCat.{0}) [Nonempty Y] :
    Function.Surjective (H0Gen.H0aug K Y).hom := by
  obtain ⟨b⟩ := ‹Nonempty Y›
  have h_surjective : Function.Surjective
      ((chainCxOf K Y).descOpcycles (H0Gen.aug K Y) 1 H0Gen.prev_zero
        (H0Gen.aug_comp_boundary_eq_zero (R := K) Y)).hom := by
    intro r
    refine ⟨(chainCxOf K Y).pOpcycles 0 (r • chainGenerator K Y 0 (pointSimplex Y b)), ?_⟩
    have hp := HomologicalComplex.p_descOpcycles (chainCxOf K Y) (H0Gen.aug K Y)
      1 H0Gen.prev_zero (H0Gen.aug_comp_boundary_eq_zero (R := K) Y)
    calc
      _ = (H0Gen.aug K Y).hom (r • chainGenerator K Y 0 (pointSimplex Y b)) :=
        congrArg (fun g => g.hom (r • chainGenerator K Y 0 (pointSimplex Y b))) hp
      _ = r := by rw [map_smul, H0Gen.aug_generator, smul_eq_mul, mul_one]
  have hι : Function.Surjective ((chainCxOf K Y).homologyι 0).hom := by
    haveI := H0Gen.isIso_homologyι_zero (R := K) Y
    exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
  have hcomp : (H0Gen.H0aug K Y).hom
      = ((chainCxOf K Y).descOpcycles (H0Gen.aug K Y) 1 H0Gen.prev_zero
          (H0Gen.aug_comp_boundary_eq_zero (R := K) Y)).hom.comp
        ((chainCxOf K Y).homologyι 0).hom := rfl
  rw [hcomp]
  exact h_surjective.comp hι

/-- **Reduced `H₀(S⁰; K)` is a line.**  Rank–nullity for the surjective augmentation. -/
theorem reducedH0_sphere0_isoOf (K : Type) [Field K] :
    Nonempty (kernel (H0Gen.H0aug K (TopCat.of (Sphere 0))) ≅ ModuleCat.of K K) := by
  have hsurj := H0augOf_surjective K (TopCat.of (Sphere 0))
  have hrank := h0_sphere0Of_finrank K
  have hker : Module.finrank K
      (LinearMap.ker (H0Gen.H0aug K (TopCat.of (Sphere 0))).hom) = 1 := by
    have hfin : Module.Finite K (homologyOf K (TopCat.of (Sphere 0)) 0) :=
      Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
    have h := LinearMap.finrank_range_add_finrank_ker
      (H0Gen.H0aug K (TopCat.of (Sphere 0))).hom
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    simp only [finrank_top, Module.finrank_self] at h
    rw [hrank] at h
    omega
  have hfinK : Module.Finite K
      (LinearMap.ker (H0Gen.H0aug K (TopCat.of (Sphere 0))).hom) :=
    Module.finite_of_finrank_pos (by rw [hker]; norm_num)
  obtain ⟨e⟩ : Nonempty (LinearMap.ker (H0Gen.H0aug K (TopCat.of (Sphere 0))).hom
      ≃ₗ[K] K) :=
    ⟨LinearEquiv.ofFinrankEq _ _ (by rw [hker, Module.finrank_self])⟩
  exact ⟨ModuleCat.kernelIsoKer _ ≪≫ e.toModuleIso⟩

/-- The kernel of the band augmentation `H₀(U ∩ V; K) → K` is a line, along the homotopy
equivalence `U ∩ V ≃ S⁰`. -/
theorem kerBand_isoOf (K : Type) [Field K] :
    Nonempty (kernel (H0Gen.subH0aug K circleTop circBand) ≅ ModuleCat.of K K) := by
  have hnat :
      (homologyIsoOfHomotopyEquivModule K (ModuleCat.of K K)
        0 (sphereBandHomotopyEquiv 0)).hom ≫
          H0Gen.H0aug K (TopCat.of (Sphere 0)) =
        H0Gen.H0aug K (TopCat.of circBand) :=
    H0Gen.H0aug_natural (TopCat.ofHom (sphereBandHomotopyEquiv 0).toFun)
  let iSub : kernel (H0Gen.subH0aug K circleTop circBand) ≅
      kernel (H0Gen.H0aug K (TopCat.of circBand)) :=
    kernelIsIsoComp
      (subspaceHomologyIso (R := K) (X := circleTop) circBand 0).hom
      (H0Gen.H0aug K (TopCat.of circBand))
  let iNat : kernel (H0Gen.H0aug K (TopCat.of circBand)) ≅
      kernel ((homologyIsoOfHomotopyEquivModule K (ModuleCat.of K K) 0
        (sphereBandHomotopyEquiv 0)).hom ≫ H0Gen.H0aug K (TopCat.of (Sphere 0))) :=
    kernelIsoOfEq hnat.symm
  let iSphere : kernel ((homologyIsoOfHomotopyEquivModule K (ModuleCat.of K K) 0
      (sphereBandHomotopyEquiv 0)).hom ≫ H0Gen.H0aug K (TopCat.of (Sphere 0))) ≅
      kernel (H0Gen.H0aug K (TopCat.of (Sphere 0))) :=
    kernelIsIsoComp
      (homologyIsoOfHomotopyEquivModule K (ModuleCat.of K K) 0
        (sphereBandHomotopyEquiv 0)).hom
      (H0Gen.H0aug K (TopCat.of (Sphere 0)))
  exact ⟨iSub ≪≫ iNat ≪≫ iSphere ≪≫ (reducedH0_sphere0_isoOf K).some⟩

/-- The Mayer–Vietoris left map on `H₀` of the circle cover, over `K`. -/
abbrev circF0Of (K : Type) [CommRing K] :
    (subChainComplex K circleTop circBand).homology 0 ⟶
      ((mvShortComplex K circU circV circUV_top).X₂).homology 0 :=
  HomologicalComplex.homologyMap (mvShortComplex K circU circV circUV_top).f 0

/-- The first biproduct projection from the Mayer–Vietoris middle term. -/
abbrev circProjUOf (K : Type) [CommRing K] :
    (mvShortComplex K circU circV circUV_top).X₂ ⟶
      subChainComplex K circleTop (circU : Set circleTop) :=
  biprod.fst

/-- The second biproduct projection from the Mayer–Vietoris middle term. -/
abbrev circProjVOf (K : Type) [CommRing K] :
    (mvShortComplex K circU circV circUV_top).X₂ ⟶
      subChainComplex K circleTop (circV : Set circleTop) :=
  biprod.snd

/-- The first injection into the Mayer–Vietoris middle term. -/
abbrev circInUOf (K : Type) [CommRing K] :
    subChainComplex K circleTop (circU : Set circleTop) ⟶
      (mvShortComplex K circU circV circUV_top).X₂ :=
  biprod.inl

/-- The second injection into the Mayer–Vietoris middle term. -/
abbrev circInVOf (K : Type) [CommRing K] :
    subChainComplex K circleTop (circV : Set circleTop) ⟶
      (mvShortComplex K circU circV circUV_top).X₂ :=
  biprod.inr

/-- The band inclusion into the upper cover member. -/
abbrev circInclUOf (K : Type) [CommRing K] :
    (mvShortComplex K circU circV circUV_top).X₁ ⟶
      subChainComplex K circleTop (circU : Set circleTop) :=
  mvInclUV_U K circU circV

/-- The band inclusion into the lower cover member. -/
abbrev circInclVOf (K : Type) [CommRing K] :
    (mvShortComplex K circU circV circUV_top).X₁ ⟶
      subChainComplex K circleTop (circV : Set circleTop) :=
  mvInclUV_V K circU circV

theorem circF_comp_fstOf (K : Type) [CommRing K] :
    (mvShortComplex K circU circV circUV_top).f ≫ circProjUOf K = circInclUOf K :=
  biprod.lift_fst _ _

theorem circF_comp_sndOf (K : Type) [CommRing K] :
    (mvShortComplex K circU circV circUV_top).f ≫ circProjVOf K = -circInclVOf K :=
  biprod.lift_snd _ _

/-- **Joint monomorphism of the homology biproduct projections.** -/
theorem biprod_homology_zero_iffOf (K : Type) [CommRing K]
    (y : ((mvShortComplex K circU circV circUV_top).X₂).homology 0) :
    y = 0 ↔
      (HomologicalComplex.homologyMap (circProjUOf K) 0) y = 0 ∧
        (HomologicalComplex.homologyMap (circProjVOf K) 0) y = 0 := by
  constructor
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩
  · rintro ⟨h1, h2⟩
    have htot :
        circProjUOf K ≫ circInUOf K + circProjVOf K ≫ circInVOf K =
          𝟙 (mvShortComplex K circU circV circUV_top).X₂ := biprod.total
    have hmap := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) htot
    simp only [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_id] at hmap
    have hy := congrArg (fun ψ => ψ y) hmap
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, h1, h2,
      map_zero, add_zero] at hy
    exact hy.symm

/-- **The Mayer–Vietoris kernel is the reduced-`H₀` kernel of the band.** -/
theorem kerF0_iso_kerBandOf (K : Type) [CommRing K] :
    Nonempty (kernel (circF0Of K) ≅ kernel (H0Gen.subH0aug K circleTop circBand)) := by
  haveI := H0Gen.isIso_subH0aug (R := K) circleTop (circU : Set circleTop)
  haveI := H0Gen.isIso_subH0aug (R := K) circleTop (circV : Set circleTop)
  have hUeq : HomologicalComplex.homologyMap (circInclUOf K) 0 ≫
      H0Gen.subH0aug K circleTop (circU : Set circleTop) =
        H0Gen.subH0aug K circleTop circBand :=
    H0Gen.subH0aug_natural_inclusion circleTop circBand
      (circU : Set circleTop) Set.inter_subset_left
  have hVeq : HomologicalComplex.homologyMap (circInclVOf K) 0 ≫
      H0Gen.subH0aug K circleTop (circV : Set circleTop) =
        H0Gen.subH0aug K circleTop circBand :=
    H0Gen.subH0aug_natural_inclusion circleTop circBand
      (circV : Set circleTop) Set.inter_subset_right
  have hfst : circF0Of K ≫ HomologicalComplex.homologyMap (circProjUOf K) 0 =
      HomologicalComplex.homologyMap (circInclUOf K) 0 := by
    have hm := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) (circF_comp_fstOf K)
    rw [HomologicalComplex.homologyMap_comp] at hm
    exact hm
  have hsnd : circF0Of K ≫ HomologicalComplex.homologyMap (circProjVOf K) 0 =
      -(HomologicalComplex.homologyMap (circInclVOf K) 0) := by
    have hm := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) (circF_comp_sndOf K)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg] at hm
    exact hm
  have hinjU : Function.Injective
      (ModuleCat.Hom.hom (H0Gen.subH0aug K circleTop (circU : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hinjV : Function.Injective
      (ModuleCat.Hom.hom (H0Gen.subH0aug K circleTop (circV : Set circleTop))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hUx : ∀ z, H0Gen.subH0aug K circleTop (circU : Set circleTop)
      ((HomologicalComplex.homologyMap (circInclUOf K) 0) z) =
        H0Gen.subH0aug K circleTop circBand z := by
    intro z
    have h := congrArg (fun ψ => ψ z) hUeq
    rwa [CategoryTheory.comp_apply] at h
  have hVx : ∀ z, H0Gen.subH0aug K circleTop (circV : Set circleTop)
      ((HomologicalComplex.homologyMap (circInclVOf K) 0) z) =
        H0Gen.subH0aug K circleTop circBand z := by
    intro z
    have h := congrArg (fun ψ => ψ z) hVeq
    rwa [CategoryTheory.comp_apply] at h
  have hfx : ∀ z, (HomologicalComplex.homologyMap (circProjUOf K) 0) (circF0Of K z) =
      (HomologicalComplex.homologyMap (circInclUOf K) 0) z := by
    intro z
    have h := congrArg (fun ψ => ψ z) hfst
    rwa [CategoryTheory.comp_apply] at h
  have hsx : ∀ z, (HomologicalComplex.homologyMap (circProjVOf K) 0) (circF0Of K z) =
      -((HomologicalComplex.homologyMap (circInclVOf K) 0) z) := by
    intro z
    have h := congrArg (fun ψ => ψ z) hsnd
    rw [CategoryTheory.comp_apply] at h
    change _ = (-(HomologicalComplex.homologyMap (circInclVOf K) 0)) z
    exact h
  have hker : LinearMap.ker (ModuleCat.Hom.hom (circF0Of K)) =
      LinearMap.ker (ModuleCat.Hom.hom (H0Gen.subH0aug K circleTop circBand)) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← hUx x, ← hfx x, hx, map_zero, map_zero]
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hax : (HomologicalComplex.homologyMap (circInclUOf K) 0) x = 0 := by
        apply hinjU
        rw [map_zero, hUx x, hx]
      have hbx : (HomologicalComplex.homologyMap (circInclVOf K) 0) x = 0 := by
        apply hinjV
        rw [map_zero, hVx x, hx]
      refine (biprod_homology_zero_iffOf K (circF0Of K x)).mpr ⟨?_, ?_⟩
      · rw [hfx x, hax]
      · rw [hsx x, hbx, neg_zero]
  exact ⟨ModuleCat.kernelIsoKer (circF0Of K) ≪≫ eqToIso (by rw [hker]) ≪≫
    (ModuleCat.kernelIsoKer (H0Gen.subH0aug K circleTop circBand)).symm⟩

/-- `H₁(S¹; K)` is the Mayer–Vietoris kernel in `H₀` of the band, by the connecting map. -/
theorem sphereH1_iso_kerF0Of (K : Type) [CommRing K] :
    Nonempty (homologyOf K (TopCat.of (Sphere 1)) 1 ≅ kernel (circF0Of K)) := by
  have hδ_mono : Mono
      ((mvShortExact K circU circV circUV_top).δ 1 0
        (by simp [ComplexShape.down_Rel])) := by
    have hzero : IsZero
        ((mvShortComplex K circU circV circUV_top).X₂.homology 1) := by
      apply isZero_mvX₂_homology
      · convert isZero_subChainComplex_homologyOf_of_contractible K
          circleTop (circU : Set circleTop) 1 (by norm_num) using 1
      · exact isZero_subChainComplex_homologyOf_of_contractible K
          circleTop (circV : Set circleTop) 1 (by norm_num)
    have hex := (mvShortExact K circU circV circUV_top).homology_exact₃
      1 0 (by simp [ComplexShape.down_Rel])
    exact hex.mono_g (hzero.eq_of_src _ _)
  have hex := (mvShortExact K circU circV circUV_top).homology_exact₁
    1 0 (by simp [ComplexShape.down_Rel])
  exact ⟨(smallChains_homologyIso K (TopCat.of (Sphere 1))
      (twoSetCover circU circV circUV_top) 1).symm ≪≫
    hex.fIsKernel.conePointUniqueUpToIso (limit.isLimit (parallelPair (circF0Of K) 0))⟩

/-- **`H₁(S¹; K) ≅ K`.** -/
def sphereOneIsoOf (K : Type) [Field K] :
    homologyOf K (TopCat.of (Sphere 1)) 1 ≅ ModuleCat.of K K :=
  (sphereH1_iso_kerF0Of K).some ≪≫ (kerF0_iso_kerBandOf K).some ≪≫ (kerBand_isoOf K).some

/-! ## 5. The top degree -/

/-- **`Hₙ(Sⁿ; K) ≅ K` for `n ≥ 1`**, by the suspension tower over the circle. -/
def sphereTopIsoOf (K : Type) [Field K] :
    (n : ℕ) → 1 ≤ n → (homologyOf K (TopCat.of (Sphere n)) n ≅ ModuleCat.of K K)
  | 0, h => absurd h (by omega)
  | 1, _ => sphereOneIsoOf K
  | (m + 2), _ =>
      (sphereSuspensionOf K (m + 1) (m + 1) (by omega)) ≪≫ sphereTopIsoOf K (m + 1) (by omega)

/-- `Hₙ(Sⁿ; K)` is one dimensional for `n ≥ 1`. -/
theorem sphereHomologyOf_top_finrank (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank K (homologyOf K (TopCat.of (Sphere n)) n) = 1 := by
  have e : homologyOf K (TopCat.of (Sphere n)) n ≃ₗ[K] K := (sphereTopIsoOf K n hn).toLinearEquiv
  rw [e.finrank_eq]
  simp

/-! ## 6. Closed endpoints -/

/-- The printed sphere computation in homology: over every field `K`, `Hₖ(Sⁿ; K)` vanishes
off `{0, n}` and `Hₙ(Sⁿ; K)` is a line for `n ≥ 1`. -/
def SphereHomologyOverField : Prop :=
  (∀ (K : Type) [Field K] (n k : ℕ), k ≠ 0 → k ≠ n →
      IsZero (homologyOf K (TopCat.of (Sphere n)) k)) ∧
    ∀ (K : Type) [Field K] (n : ℕ), 1 ≤ n →
      Nonempty (homologyOf K (TopCat.of (Sphere n)) n ≅ ModuleCat.of K K)

theorem sphereHomologyOverField : SphereHomologyOverField := by
  refine ⟨?_, ?_⟩
  · intro K _ n k h0 hkn
    exact sphereHomologyOf_isZero_of_ne K n k h0 hkn
  · intro K _ n hn
    exact ⟨sphereTopIsoOf K n hn⟩

#audit_closed_axioms sphereHomologyOverField

end CharClass
end GroupApproximation

end
