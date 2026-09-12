import GroupApproximation.CharClass.MayerVietorisElement

/-!
# The Mayer–Vietoris long exact sequence in element form, with coefficients in a field

The coefficient-generic form of `MayerVietorisElement`.  For two opens `U ⊔ V = ⊤` of `X`
and a field `K`, this file produces the four restriction maps and the three exactness
statements of cohomological Mayer–Vietoris as statements about elements:

```text
H^n(X; K) → H^n(U; K) ⊕ H^n(V; K) → H^n(U ∩ V; K) →^δ H^{n+1}(X; K) → ⋯
```

The categorical input is `CohomologyMayerVietoris`' generic `mvCoSCOf K`, its short
exactness and the three homology exactness statements `mvExactOf_ambient`, `mvExactOf_sum`,
`mvExactOf_inter`; the identification of the middle term with a sum of two pieces is
`MayerVietorisBiproduct.mvH_decomposeOf`.  A field is needed only because the ambient
identification `mvAmbientIsoOf` (the dual of the small-chain inclusion is a
quasi-isomorphism) asks for one.

## The sign, which over `F₂` was invisible

The chain-level Mayer–Vietoris map is `biprod.lift ι (−ι')`, so the composite
`H^n(V) → H^n(C^*(U) ⊕ C^*(V)) → H^n(U ∩ V)` through the middle term is **minus** the
restriction.  Over `F₂` the minus is the identity and `MayerVietorisElement` reads the
composite as the restriction.  Over `K` it is not, so `mvResWVOf` is the **negative** of the
composite, which makes it the honest restriction, and then:

* `mvExactSumOf` says that two classes come from one global class exactly when their honest
  restrictions to `U ∩ V` **agree** (the middle map is the difference);
* `mvExactWOf` keeps the `+` of `MVSequenceOf.exact_W`: the image of the difference
  `(a, b) ↦ a| − b|` is the set of sums `a| + b'|`, since `b ↦ −b` is a bijection.

## Main declarations

* `mvPhiOf`, `mvPsiOf` — the two structural maps.
* `mvResUOf`, `mvResVOf`, `mvResWUOf`, `mvResWVOf` — the four restrictions.
* `mvExactXOf`, `mvExactSumOf`, `mvExactWOf` — exactness at the three spots.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-! ## 0. Small bridges over any coefficient ring -/

/-- Exactness of a short complex of `K`-modules, in element form. -/
theorem mvExists_of_exactOf {K : Type} [CommRing K] {S : ShortComplex (ModuleCat.{0} K)}
    (hS : S.Exact) {m : S.X₂} (hm : S.g.hom m = 0) : ∃ e : S.X₁, S.f.hom e = m := by
  have hmem : m ∈ LinearMap.ker S.g.hom := hm
  rw [← hS.moduleCat_range_eq_ker] at hmem
  exact LinearMap.mem_range.1 hmem

/-- An isomorphism of `K`-modules does not kill anything. -/
theorem eq_zero_of_iso_hom_eq_zeroOf {K : Type} [CommRing K] {M N : ModuleCat.{0} K}
    (e : M ≅ N) {x : M} (h : e.hom.hom x = 0) : x = 0 := by
  have h1 : e.inv.hom (e.hom.hom x) = x := hom_apply_of_comp_eq_id e.hom_inv_id x
  rw [h, map_zero] at h1
  exact h1.symm

theorem iso_inv_hom_applyOf {K : Type} [CommRing K] {M N : ModuleCat.{0} K} (e : M ≅ N)
    (x : M) : e.inv.hom (e.hom.hom x) = x := hom_apply_of_comp_eq_id e.hom_inv_id x

theorem iso_hom_inv_applyOf {K : Type} [CommRing K] {M N : ModuleCat.{0} K} (e : M ≅ N)
    (y : N) : e.hom.hom (e.inv.hom y) = y := hom_apply_of_comp_eq_id e.inv_hom_id y

/-! ## 1. The two structural maps -/

/-- `H^n(X; K) → H^n(C^*(U) ⊕ C^*(V))`, the first map of the dual Mayer–Vietoris
sequence with its source identified. -/
def mvPhiOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod K X n ⟶ (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n :=
  (mvAmbientIsoOf K U V hUV n).inv ≫ HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n

/-- `H^n(C^*(U) ⊕ C^*(V)) → H^n(U ∩ V; K)`, the second map of the dual Mayer–Vietoris
sequence with its target identified. -/
def mvPsiOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n ⟶ Hmod K (mvInter U V) n :=
  HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n ≫ (mvInterIsoOf K U V hUV n).hom

theorem mvPsiOf_mvPhiOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (y : Hmod K X n) : (mvPsiOf K U V hUV n).hom ((mvPhiOf K U V hUV n).hom y) = 0 := by
  have hFG : HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n
      ≫ HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, (mvCoSCOf K U V hUV).zero,
      HomologicalComplex.homologyMap_zero]
  have hpt : ∀ e : (mvCoSCOf K U V hUV).X₁.homology n,
      (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n).hom
        ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n).hom e) = 0 := by
    intro e
    have h := hom_apply_of_comp_eq hFG e
    rw [h]; rfl
  show (mvInterIsoOf K U V hUV n).hom.hom
    ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n).hom
      ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n).hom
        ((mvAmbientIsoOf K U V hUV n).inv.hom y))) = 0
  rw [hpt, map_zero]

/-! ## 2. The four restrictions -/

/-- Restriction `H^n(X; K) → H^n(U; K)`. -/
def mvResUOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod K X n ⟶ Hmod K (mvU U) n :=
  mvPhiOf K U V hUV n ≫ mvHProjUOf K U V n ≫ (subCxDualHomologyIsoOf K (U : Set X) n).hom

/-- Restriction `H^n(X; K) → H^n(V; K)`. -/
def mvResVOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod K X n ⟶ Hmod K (mvU V) n :=
  mvPhiOf K U V hUV n ≫ mvHProjVOf K U V n ≫ (subCxDualHomologyIsoOf K (V : Set X) n).hom

/-- Restriction `H^n(U; K) → H^n(U ∩ V; K)`. -/
def mvResWUOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod K (mvU U) n ⟶ Hmod K (mvInter U V) n :=
  (subCxDualHomologyIsoOf K (U : Set X) n).inv ≫ mvHInclUOf K U V n ≫ mvPsiOf K U V hUV n

/-- Restriction `H^n(V; K) → H^n(U ∩ V; K)`.  The composite through the middle term is
**minus** the restriction, because the chain-level map is `biprod.lift ι (−ι')`; this is
its negative. -/
def mvResWVOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod K (mvU V) n ⟶ Hmod K (mvInter U V) n :=
  -((subCxDualHomologyIsoOf K (V : Set X) n).inv ≫ mvHInclVOf K U V n ≫ mvPsiOf K U V hUV n)

theorem mvResUOf_apply (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : Hmod K X n) :
    (mvResUOf K U V hUV n).hom x
      = (subCxDualHomologyIsoOf K (U : Set X) n).hom.hom
          ((mvHProjUOf K U V n).hom ((mvPhiOf K U V hUV n).hom x)) := rfl

theorem mvResVOf_apply (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : Hmod K X n) :
    (mvResVOf K U V hUV n).hom x
      = (subCxDualHomologyIsoOf K (V : Set X) n).hom.hom
          ((mvHProjVOf K U V n).hom ((mvPhiOf K U V hUV n).hom x)) := rfl

theorem mvResWUOf_apply (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (a : Hmod K (mvU U) n) :
    (mvResWUOf K U V hUV n).hom a
      = (mvPsiOf K U V hUV n).hom
          ((mvHInclUOf K U V n).hom ((subCxDualHomologyIsoOf K (U : Set X) n).inv.hom a)) :=
  rfl

theorem mvResWVOf_apply (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (b : Hmod K (mvU V) n) :
    (mvResWVOf K U V hUV n).hom b
      = -(mvPsiOf K U V hUV n).hom
          ((mvHInclVOf K U V n).hom ((subCxDualHomologyIsoOf K (V : Set X) n).inv.hom b)) :=
  rfl

/-- The two components of `mvPhiOf x` are the two restrictions of `x`. -/
theorem mvPhiOf_eq_zero_iff (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : Hmod K X n) :
    (mvPhiOf K U V hUV n).hom x = 0
      ↔ ((mvResUOf K U V hUV n).hom x = 0 ∧ (mvResVOf K U V hUV n).hom x = 0) := by
  rw [mvH_eq_zero_iffOf K U V n]
  constructor
  · rintro ⟨hU, hV⟩
    refine ⟨?_, ?_⟩
    · rw [mvResUOf_apply, hU, map_zero]
    · rw [mvResVOf_apply, hV, map_zero]
  · rintro ⟨hU, hV⟩
    rw [mvResUOf_apply] at hU
    rw [mvResVOf_apply] at hV
    exact ⟨eq_zero_of_iso_hom_eq_zeroOf _ hU, eq_zero_of_iso_hom_eq_zeroOf _ hV⟩

/-! ## 3. Exactness at the three spots -/

/-- **Exactness at `H^{n+1}(X; K)`.**  A class restricting to zero on both pieces is in
the image of the connecting map. -/
theorem mvExactXOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : Hmod K X (n + 1)) :
    ((mvResUOf K U V hUV (n + 1)).hom x = 0 ∧ (mvResVOf K U V hUV (n + 1)).hom x = 0)
      ↔ ∃ w, (mvDeltaOf K U V hUV n).hom w = x := by
  have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by simp
  rw [← mvPhiOf_eq_zero_iff]
  constructor
  · intro hx
    have hker : (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f (n + 1)).hom
        ((mvAmbientIsoOf K U V hUV (n + 1)).inv.hom x) = 0 := hx
    obtain ⟨d, hd⟩ := mvExists_of_exactOf (mvExactOf_ambient K U V hUV n) hker
    refine ⟨(mvInterIsoOf K U V hUV n).hom.hom d, ?_⟩
    show (mvAmbientIsoOf K U V hUV (n + 1)).hom.hom
      (((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) hrel).hom
        ((mvInterIsoOf K U V hUV n).inv.hom ((mvInterIsoOf K U V hUV n).hom.hom d))) = x
    rw [iso_inv_hom_applyOf, hd, iso_hom_inv_applyOf]
  · rintro ⟨w, rfl⟩
    have hzero : ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) hrel)
        ≫ HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f (n + 1) = 0 :=
      (mvCoSCOf_shortExact K U V hUV).δ_comp n (n + 1) hrel
    show (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f (n + 1)).hom
      ((mvAmbientIsoOf K U V hUV (n + 1)).inv.hom
        ((mvAmbientIsoOf K U V hUV (n + 1)).hom.hom
          (((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) hrel).hom
            ((mvInterIsoOf K U V hUV n).inv.hom w)))) = 0
    rw [iso_inv_hom_applyOf, hom_apply_of_comp_eq hzero]
    rfl

/-- **Exactness at `H^n(U; K) ⊕ H^n(V; K)`.**  Two classes whose restrictions to the
intersection agree come from a global class. -/
theorem mvExactSumOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (a : Hmod K (mvU U) n) (b : Hmod K (mvU V) n) :
    (mvResWUOf K U V hUV n).hom a = (mvResWVOf K U V hUV n).hom b
      ↔ ∃ x : Hmod K X n,
          (mvResUOf K U V hUV n).hom x = a ∧ (mvResVOf K U V hUV n).hom x = b := by
  set m : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n :=
    (mvHInclUOf K U V n).hom ((subCxDualHomologyIsoOf K (U : Set X) n).inv.hom a)
      + (mvHInclVOf K U V n).hom ((subCxDualHomologyIsoOf K (V : Set X) n).inv.hom b) with hm
  have hpsi : (mvPsiOf K U V hUV n).hom m
      = (mvResWUOf K U V hUV n).hom a - (mvResWVOf K U V hUV n).hom b := by
    rw [hm, map_add, mvResWUOf_apply, mvResWVOf_apply, sub_neg_eq_add]
  have hprojU : (mvHProjUOf K U V n).hom m
      = (subCxDualHomologyIsoOf K (U : Set X) n).inv.hom a := by
    rw [hm, map_add, mvH_inclU_projUOf, mvH_inclV_projUOf, add_zero]
  have hprojV : (mvHProjVOf K U V n).hom m
      = (subCxDualHomologyIsoOf K (V : Set X) n).inv.hom b := by
    rw [hm, map_add, mvH_inclU_projVOf, mvH_inclV_projVOf, zero_add]
  constructor
  · intro hab
    have hzero : (mvPsiOf K U V hUV n).hom m = 0 := by
      rw [hpsi, hab, sub_self]
    have hg : (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n).hom m = 0 :=
      eq_zero_of_iso_hom_eq_zeroOf (mvInterIsoOf K U V hUV n) hzero
    obtain ⟨e, he⟩ := mvExists_of_exactOf (mvExactOf_sum K U V hUV n) hg
    refine ⟨(mvAmbientIsoOf K U V hUV n).hom.hom e, ?_, ?_⟩
    · rw [mvResUOf_apply]
      show (subCxDualHomologyIsoOf K (U : Set X) n).hom.hom ((mvHProjUOf K U V n).hom
        ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n).hom
          ((mvAmbientIsoOf K U V hUV n).inv.hom ((mvAmbientIsoOf K U V hUV n).hom.hom e)))) = a
      rw [iso_inv_hom_applyOf, he, hprojU, iso_hom_inv_applyOf]
    · rw [mvResVOf_apply]
      show (subCxDualHomologyIsoOf K (V : Set X) n).hom.hom ((mvHProjVOf K U V n).hom
        ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n).hom
          ((mvAmbientIsoOf K U V hUV n).inv.hom ((mvAmbientIsoOf K U V hUV n).hom.hom e)))) = b
      rw [iso_inv_hom_applyOf, he, hprojV, iso_hom_inv_applyOf]
  · rintro ⟨x, hxa, hxb⟩
    have hU : (mvHProjUOf K U V n).hom ((mvPhiOf K U V hUV n).hom x)
        = (subCxDualHomologyIsoOf K (U : Set X) n).inv.hom a := by
      rw [← hxa, mvResUOf_apply, iso_inv_hom_applyOf]
    have hV : (mvHProjVOf K U V n).hom ((mvPhiOf K U V hUV n).hom x)
        = (subCxDualHomologyIsoOf K (V : Set X) n).inv.hom b := by
      rw [← hxb, mvResVOf_apply, iso_inv_hom_applyOf]
    have hdec : (mvPhiOf K U V hUV n).hom x = m := by
      rw [hm, ← hU, ← hV, mvH_decomposeOf]
    have h0 : (mvResWUOf K U V hUV n).hom a - (mvResWVOf K U V hUV n).hom b = 0 := by
      rw [← hpsi, ← hdec]; exact mvPsiOf_mvPhiOf K U V hUV n x
    exact sub_eq_zero.mp h0

/-- **Exactness at `H^n(U ∩ V; K)`.**  A class killed by the connecting map is a sum of
restrictions. -/
theorem mvExactWOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (w : Hmod K (mvInter U V) n) :
    (mvDeltaOf K U V hUV n).hom w = 0
      ↔ ∃ (a : Hmod K (mvU U) n) (b : Hmod K (mvU V) n),
          (mvResWUOf K U V hUV n).hom a + (mvResWVOf K U V hUV n).hom b = w := by
  have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by simp
  constructor
  · intro hw
    have hd : ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) hrel).hom
        ((mvInterIsoOf K U V hUV n).inv.hom w) = 0 :=
      eq_zero_of_iso_hom_eq_zeroOf (mvAmbientIsoOf K U V hUV (n + 1)) hw
    obtain ⟨m, hmm⟩ := mvExists_of_exactOf (mvExactOf_inter K U V hUV n) hd
    refine ⟨(subCxDualHomologyIsoOf K (U : Set X) n).hom.hom ((mvHProjUOf K U V n).hom m),
      -(subCxDualHomologyIsoOf K (V : Set X) n).hom.hom ((mvHProjVOf K U V n).hom m), ?_⟩
    rw [mvResWUOf_apply, mvResWVOf_apply]
    simp only [map_neg, neg_neg, iso_inv_hom_applyOf]
    rw [← map_add, mvH_decomposeOf]
    show (mvInterIsoOf K U V hUV n).hom.hom
      ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n).hom m) = w
    rw [hmm, iso_hom_inv_applyOf]
  · rintro ⟨a, b, hab⟩
    set m : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).homology n :=
      (mvHInclUOf K U V n).hom ((subCxDualHomologyIsoOf K (U : Set X) n).inv.hom a)
        - (mvHInclVOf K U V n).hom ((subCxDualHomologyIsoOf K (V : Set X) n).inv.hom b)
      with hm
    have hpsi : (mvPsiOf K U V hUV n).hom m = w := by
      rw [hm, map_sub, ← hab, mvResWUOf_apply, mvResWVOf_apply, sub_eq_add_neg]
    have hg : (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n).hom m
        = (mvInterIsoOf K U V hUV n).inv.hom w := by
      rw [← hpsi]
      show _ = (mvInterIsoOf K U V hUV n).inv.hom ((mvInterIsoOf K U V hUV n).hom.hom
        ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n).hom m))
      rw [iso_inv_hom_applyOf]
    have hzero : ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) hrel).hom
        ((mvInterIsoOf K U V hUV n).inv.hom w) = 0 := by
      rw [← hg]
      have hcomp : HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n
          ≫ ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) hrel) = 0 :=
        (mvCoSCOf_shortExact K U V hUV).comp_δ n (n + 1) hrel
      rw [hom_apply_of_comp_eq hcomp]; rfl
    show (mvAmbientIsoOf K U V hUV (n + 1)).hom.hom
      (((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) hrel).hom
        ((mvInterIsoOf K U V hUV n).inv.hom w)) = 0
    rw [hzero, map_zero]

end

end GroupApproximation.CharClass
