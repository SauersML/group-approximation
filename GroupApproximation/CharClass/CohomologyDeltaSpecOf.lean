import GroupApproximation.CharClass.CohomologyDeltaLiftOf
import GroupApproximation.CharClass.MayerVietorisPullOf

/-!
# The Mayer–Vietoris connecting map over a field, computed on cochains

The coefficient-generic forms of `CohomologyDeltaChain`, `CohomologyDeltaSpec` and
`CohomologyDeltaValue`.  Given a cocycle `α` on `U ∩ V`, cochains `α_U`, `α_V` on the two
pieces with

```text
α_U|_{U∩V} − α_V|_{U∩V} = α,
```

and a cochain `γ` on the ambient space restricting to `d α_U` on `U` and to `d α_V` on `V`,
the connecting map takes the class of `α` to the class of `γ` (`mvDeltaOf_spec`); and such
data exists for every class (`mvDeltaOf_data`).

## The sign

Over `F₂` the condition reads `α_U| + α_V| = α`.  Over `K` the second map of the dual
sequence is the dual of `biprod.lift ι (−ι')`, so on the lift `eltU α_U + eltV α_V` it takes
the value `α_U| − α_V|` (`mvGmid_eltUOf`, `mvGmid_eltVOf`), and the condition carries the
difference.
The two restriction conditions on `γ` carry no sign: the first map is `biprod.desc`.

A field is needed only for the ambient identification `mvAmbientIsoOf` and for the
surjectivity of the restriction of global cochains to the small chains (`K` is injective over
itself).
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X : TopCat.{0}}

/-! ## 1. Cochains as elements of the terms of the sequence -/

/-- A cochain on the subspace `S`, as an element of the dual of the subordinate chains of
`S`. -/
def eltSubOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    (a : singularCochainGroup K (TopCat.of S) p) :
    (dualCxOf K (subChainComplex K X S)).X p :=
  (((subCxDualIsoOf K S).inv).f p).hom a

@[simp] theorem hom_eltSubOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    (a : singularCochainGroup K (TopCat.of S) p) :
    (((subCxDualIsoOf K S).hom).f p).hom (eltSubOf K S p a) = a := by
  rw [eltSubOf, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    (subCxDualIsoOf K S).inv_hom_id, HomologicalComplex.id_f]
  rfl

@[simp] theorem dualMapOf_corestrict_eltSubOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    (a : singularCochainGroup K (TopCat.of S) p) :
    ((dualMapOf K (subChainCorestrict K X S)).f p).hom (eltSubOf K S p a) = a :=
  hom_eltSubOf K S p a

theorem eltSub_injectiveOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    {a b : singularCochainGroup K (TopCat.of S) p} (h : eltSubOf K S p a = eltSubOf K S p b) :
    a = b := by
  have := congrArg (((subCxDualIsoOf K S).hom).f p).hom h
  rwa [hom_eltSubOf, hom_eltSubOf] at this

theorem eltSub_extOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    {z w : (dualCxOf K (subChainComplex K X S)).X p}
    (h : (((subCxDualIsoOf K S).hom).f p).hom z = (((subCxDualIsoOf K S).hom).f p).hom w) :
    z = w :=
  (ModuleCat.mono_iff_injective (((subCxDualIsoOf K S).hom).f p)).1 inferInstance h

theorem eltSub_homOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    (z : (dualCxOf K (subChainComplex K X S)).X p) :
    eltSubOf K S p ((((subCxDualIsoOf K S).hom).f p).hom z) = z := by
  rw [eltSubOf, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    (subCxDualIsoOf K S).hom_inv_id, HomologicalComplex.id_f]
  rfl

theorem eltSub_zeroOf (K : Type) [CommRing K] (S : Set X) (p : ℕ) :
    eltSubOf K S p 0 = 0 := map_zero _

theorem eltSub_subOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    (a b : singularCochainGroup K (TopCat.of S) p) :
    eltSubOf K S p (a - b) = eltSubOf K S p a - eltSubOf K S p b := map_sub _ _ _

/-- `eltSubOf` commutes with the coboundary. -/
theorem d_eltSubOf (K : Type) [CommRing K] (S : Set X) (p : ℕ)
    (a : singularCochainGroup K (TopCat.of S) p) :
    ((dualCxOf K (subChainComplex K X S)).d p (p + 1)).hom (eltSubOf K S p a)
      = eltSubOf K S (p + 1) (cochainCoboundary K (TopCat.of S) p a) := by
  have hcomm := ((subCxDualIsoOf K S).inv).comm p (p + 1)
  have h := congrArg (fun ψ => ψ.hom a) hcomm
  simp only [ModuleCat.comp_apply] at h
  exact h

/-- A cochain on `U`, as an element of the middle term. -/
def eltUOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (aU : singularCochainGroup K (TopCat.of (U : Set X)) p) :
    (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p :=
  ((mvCxInclUOf K U V).f p).hom (eltSubOf K (U : Set X) p aU)

/-- A cochain on `V`, as an element of the middle term. -/
def eltVOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (aV : singularCochainGroup K (TopCat.of (V : Set X)) p) :
    (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p :=
  ((mvCxInclVOf K U V).f p).hom (eltSubOf K (V : Set X) p aV)

/-- A cochain on the ambient space, as an element of the first term. -/
def eltAmbOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (c : singularCochainGroup K X p) : (mvCoSCOf K U V hUV).X₁.X p :=
  ((dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))).f p).hom c

/-! ## 2. The two maps of the sequence on those elements -/

/-- The second map of the dual sequence, with its source written explicitly. -/
def mvGmidOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p
      ⟶ (dualCxOf K (subChainComplex K X ((U : Set X) ∩ (V : Set X)))).X p :=
  (mvCoSCOf K U V hUV).g.f p

/-- The first map of the dual sequence, with its target written explicitly. -/
def mvFmidOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (mvCoSCOf K U V hUV).X₁.X p ⟶ (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p :=
  (mvCoSCOf K U V hUV).f.f p

theorem mvGmid_eltUOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (aU : singularCochainGroup K (TopCat.of (U : Set X)) p) :
    (mvGmidOf K U V hUV p).hom (eltUOf K U V p aU)
      = eltSubOf K ((U : Set X) ∩ (V : Set X)) p
          (cochainPullback (subInclusion Set.inter_subset_left) p aU) := by
  have hcx : (mvCxInclUOf K U V ≫ (mvCoSCOf K U V hUV).g)
        ≫ dualMapOf K (subChainCorestrict K X ((U : Set X) ∩ (V : Set X)))
      = dualMapOf K (subChainCorestrict K X (U : Set X))
        ≫ dualMapOf K ((chainCxFunOf K).map (subInclusion Set.inter_subset_left)) := by
    rw [mvCxInclUOf_comp_g]
    exact dualMapOf_subChainCorestrict_naturality K Set.inter_subset_left
  refine eltSub_extOf K _ p ?_
  rw [hom_eltSubOf]
  have h := congrArg (fun φ => ((φ.f p).hom (eltSubOf K (U : Set X) p aU))) hcx
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    dualMapOf_corestrict_eltSubOf] at h
  exact h

/-- The `V` twin, where the sign of the chain-level map survives. -/
theorem mvGmid_eltVOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (aV : singularCochainGroup K (TopCat.of (V : Set X)) p) :
    (mvGmidOf K U V hUV p).hom (eltVOf K U V p aV)
      = -eltSubOf K ((U : Set X) ∩ (V : Set X)) p
          (cochainPullback (subInclusion Set.inter_subset_right) p aV) := by
  -- The sign is moved out on elements; `Preadditive.neg_comp` does not match a composite whose
  -- middle object is spelled `(mvCoSCOf K U V hUV).X₃` under instance transparency.
  have h1 : (mvCxInclVOf K U V).f p ≫ (mvCoSCOf K U V hUV).g.f p
      = (mvCxInclVOf K U V ≫ (mvCoSCOf K U V hUV).g).f p :=
    (HomologicalComplex.comp_f _ _ p).symm
  rw [mvCxInclVOf_comp_g] at h1
  have h2 : (mvGmidOf K U V hUV p).hom (eltVOf K U V p aV)
      = -((dualMapOf K (subChainInclusion (R := K) ((U : Set X) ∩ (V : Set X)) (V : Set X)
          Set.inter_subset_right)).f p).hom (eltSubOf K (V : Set X) p aV) :=
    (hom_apply_of_comp_eq h1 (eltSubOf K (V : Set X) p aV)).trans rfl
  rw [h2]
  refine congrArg Neg.neg ?_
  refine eltSub_extOf K _ p ?_
  rw [hom_eltSubOf]
  have hnat := congrArg (fun φ => ((φ.f p).hom (eltSubOf K (V : Set X) p aV)))
    (dualMapOf_subChainCorestrict_naturality K
      (Set.inter_subset_right (s := (U : Set X)) (t := (V : Set X))))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    dualMapOf_corestrict_eltSubOf] at hnat
  exact hnat

/-- Two elements of the middle term agree once their two components do. -/
theorem mvX2_extOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    {z w : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p}
    (hU : ((mvCxProjUOf K U V).f p).hom z = ((mvCxProjUOf K U V).f p).hom w)
    (hV : ((mvCxProjVOf K U V).f p).hom z = ((mvCxProjVOf K U V).f p).hom w) : z = w := by
  have htot := congrArg (fun φ : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V))
      ⟶ (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)) =>
    ((φ.f p).hom z, (φ.f p).hom w)) (mvCxOf_total K U V)
  simp only [Prod.mk.injEq] at htot
  have hz : z = ((mvCxInclUOf K U V).f p).hom (((mvCxProjUOf K U V).f p).hom z)
      + ((mvCxInclVOf K U V).f p).hom (((mvCxProjVOf K U V).f p).hom z) := by
    have := htot.1
    simpa [ModuleCat.comp_apply] using this.symm
  have hw : w = ((mvCxInclUOf K U V).f p).hom (((mvCxProjUOf K U V).f p).hom w)
      + ((mvCxInclVOf K U V).f p).hom (((mvCxProjVOf K U V).f p).hom w) := by
    have := htot.2
    simpa [ModuleCat.comp_apply] using this.symm
  rw [hz, hw, hU, hV]

theorem projU_eltUOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (aU : singularCochainGroup K (TopCat.of (U : Set X)) p) :
    ((mvCxProjUOf K U V).f p).hom (eltUOf K U V p aU) = eltSubOf K (U : Set X) p aU := by
  rw [eltUOf, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclUOf_projU,
    HomologicalComplex.id_f]
  rfl

theorem projU_eltVOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (aV : singularCochainGroup K (TopCat.of (V : Set X)) p) :
    ((mvCxProjUOf K U V).f p).hom (eltVOf K U V p aV) = 0 := by
  rw [eltVOf, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclVOf_projU]
  rfl

theorem projV_eltVOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (aV : singularCochainGroup K (TopCat.of (V : Set X)) p) :
    ((mvCxProjVOf K U V).f p).hom (eltVOf K U V p aV) = eltSubOf K (V : Set X) p aV := by
  rw [eltVOf, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclVOf_projV,
    HomologicalComplex.id_f]
  rfl

theorem projV_eltUOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (aU : singularCochainGroup K (TopCat.of (U : Set X)) p) :
    ((mvCxProjVOf K U V).f p).hom (eltUOf K U V p aU) = 0 := by
  rw [eltUOf, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclUOf_projV]
  rfl

theorem projU_mvFmid_eltAmbOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (p : ℕ) (c : singularCochainGroup K X p) :
    ((mvCxProjUOf K U V).f p).hom ((mvFmidOf K U V hUV p).hom (eltAmbOf K U V hUV p c))
      = eltSubOf K (U : Set X) p (cochainPullback (sInclusion (U : Set X)) p c) := by
  have hA := congrArg (fun φ => ((φ.f p).hom (eltAmbOf K U V hUV p c)))
    (f_comp_mvCxProjUOf K U V hUV)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hA
  have hcx : dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))
        ≫ dualMapOf K (mvInclU_small K U V hUV)
        ≫ dualMapOf K (subChainCorestrict K X (U : Set X))
      = dualMapOf K ((chainCxFunOf K).map (sInclusion (U : Set X))) := by
    rw [← Category.assoc, mvDualMapOf_comp, mvDualMapOf_comp]
    exact congrArg (fun φ => dualMapOf K φ) (subChainCorestrict_comp_toAllOf K U V hUV)
  refine eltSub_extOf K _ p ?_
  rw [hom_eltSubOf]
  have h := congrArg (fun φ => ((φ.f p).hom c)) hcx
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  exact (congrArg ((subCxDualIsoOf K ((U : Opens X) : Set X)).hom.f p).hom hA).trans h

theorem projV_mvFmid_eltAmbOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (p : ℕ) (c : singularCochainGroup K X p) :
    ((mvCxProjVOf K U V).f p).hom ((mvFmidOf K U V hUV p).hom (eltAmbOf K U V hUV p c))
      = eltSubOf K (V : Set X) p (cochainPullback (sInclusion (V : Set X)) p c) := by
  have hA := congrArg (fun φ => ((φ.f p).hom (eltAmbOf K U V hUV p c)))
    (f_comp_mvCxProjVOf K U V hUV)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hA
  have hcx : dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))
        ≫ dualMapOf K (mvInclV_small K U V hUV)
        ≫ dualMapOf K (subChainCorestrict K X (V : Set X))
      = dualMapOf K ((chainCxFunOf K).map (sInclusion (V : Set X))) := by
    rw [← Category.assoc, mvDualMapOf_comp, mvDualMapOf_comp]
    exact congrArg (fun φ => dualMapOf K φ) (subChainCorestrict_comp_toAllVOf K U V hUV)
  refine eltSub_extOf K _ p ?_
  rw [hom_eltSubOf]
  have h := congrArg (fun φ => ((φ.f p).hom c)) hcx
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  exact (congrArg ((subCxDualIsoOf K ((V : Opens X) : Set X)).hom.f p).hom hA).trans h

/-! ## 3. The maps commute with the differential -/

theorem projU_dOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (z : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p) :
    ((mvCxProjUOf K U V).f (p + 1)).hom
        (((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom z)
      = ((dualCxOf K (mvCxOf K U)).d p (p + 1)).hom (((mvCxProjUOf K U V).f p).hom z) := by
  have h := congrArg (fun ψ => ψ.hom z) ((mvCxProjUOf K U V).comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem projV_dOf (K : Type) [CommRing K] (U V : Opens X) (p : ℕ)
    (z : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p) :
    ((mvCxProjVOf K U V).f (p + 1)).hom
        (((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom z)
      = ((dualCxOf K (mvCxOf K V)).d p (p + 1)).hom (((mvCxProjVOf K U V).f p).hom z) := by
  have h := congrArg (fun ψ => ψ.hom z) ((mvCxProjVOf K U V).comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem g_dOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (z : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p) :
    (mvGmidOf K U V hUV (p + 1)).hom
        (((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom z)
      = ((dualCxOf K (subChainComplex K X ((U : Set X) ∩ (V : Set X)))).d p (p + 1)).hom
          ((mvGmidOf K U V hUV p).hom z) := by
  have h := congrArg (fun ψ => ψ.hom z) ((mvCoSCOf K U V hUV).g.comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem f_dOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (w : (mvCoSCOf K U V hUV).X₁.X p) :
    (mvFmidOf K U V hUV (p + 1)).hom (((mvCoSCOf K U V hUV).X₁.d p (p + 1)).hom w)
      = ((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom
          ((mvFmidOf K U V hUV p).hom w) := by
  have h := congrArg (fun ψ => ψ.hom w) ((mvCoSCOf K U V hUV).f.comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem g_f_applyOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (w : (mvCoSCOf K U V hUV).X₁.X p) :
    (mvGmidOf K U V hUV p).hom ((mvFmidOf K U V hUV p).hom w) = 0 := by
  have h : (mvCoSCOf K U V hUV).f.f p ≫ (mvCoSCOf K U V hUV).g.f p
      = (0 : (mvCoSCOf K U V hUV).X₁.X p ⟶ (mvCoSCOf K U V hUV).X₃.X p) := by
    rw [← HomologicalComplex.comp_f, (mvCoSCOf K U V hUV).zero, HomologicalComplex.zero_f]
  have h2 := congrArg (fun ψ => ψ.hom w) h
  simp only [ModuleCat.comp_apply] at h2
  exact h2

/-! ## 4. The splitting -/

/-- A degreewise section of the second map of the dual sequence. -/
def mvSectGOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (dualCxOf K (subChainComplex K X ((U : Set X) ∩ (V : Set X)))).X p
      ⟶ (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p :=
  (mvCoSplittingOf K U V hUV p).s

/-- A degreewise retraction of the first map of the dual sequence. -/
def mvRetrFOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p ⟶ (mvCoSCOf K U V hUV).X₁.X p :=
  (mvCoSplittingOf K U V hUV p).r

theorem mvSectG_gOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (y : (dualCxOf K (subChainComplex K X ((U : Set X) ∩ (V : Set X)))).X p) :
    (mvGmidOf K U V hUV p).hom ((mvSectGOf K U V hUV p).hom y) = y := by
  have h := congrArg (fun ψ => ψ.hom y) (mvCoSplittingOf K U V hUV p).s_g
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h
  exact h

theorem f_mvRetrFOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (z : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p) (hz : (mvGmidOf K U V hUV p).hom z = 0) :
    (mvFmidOf K U V hUV p).hom ((mvRetrFOf K U V hUV p).hom z) = z := by
  have h := congrArg (fun ψ => ψ.hom z) (mvCoSplittingOf K U V hUV p).id
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at h
  have h2 : (mvFmidOf K U V hUV p).hom ((mvRetrFOf K U V hUV p).hom z)
      + ((mvSectGOf K U V hUV p).hom ((mvGmidOf K U V hUV p).hom z)) = z := h
  rw [hz, map_zero, add_zero] at h2
  exact h2

/-! ## 5. Cocycles with the same class differ by a coboundary -/

/-- The short complex `C^n → Z^{n+1} → H^{n+1}` of a cochain complex. -/
def clsSCOf {R : Type} [CommRing R] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    ShortComplex (ModuleCat.{0} R) :=
  ShortComplex.mk (C.toCycles n (n + 1)) (C.homologyπ (n + 1))
    (C.toCycles_comp_homologyπ n (n + 1))

theorem clsSC_exactOf {R : Type} [CommRing R] (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) : (clsSCOf C n).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (C.homologyIsCokernel n (n + 1) (ComplexShape.prev_eq' _ (upRel n)))

/-- **Two cocycles with the same class differ by a coboundary**, over any ring. -/
theorem exists_d_of_clsOfK_eq {R : Type} [CommRing R] (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (z z' : C.X (n + 1))
    (hz : (C.d (n + 1) (n + 2)).hom z = 0) (hz' : (C.d (n + 1) (n + 2)).hom z' = 0)
    (h : CohClass.clsOfK C (n + 1) z hz = CohClass.clsOfK C (n + 1) z' hz') :
    ∃ w : C.X n, z = z' + (C.d n (n + 1)).hom w := by
  have hnext : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
    ComplexShape.next_eq' _ (upRel (n + 1))
  have hπ : ((clsSCOf C n).g).hom
      (C.cyclesMk z (n + 2) hnext hz - C.cyclesMk z' (n + 2) hnext hz') = 0 := by
    refine (map_sub ((clsSCOf C n).g).hom (C.cyclesMk z (n + 2) hnext hz)
      (C.cyclesMk z' (n + 2) hnext hz')).trans ?_
    exact sub_eq_zero_of_eq h
  obtain ⟨w, hw⟩ :=
    (ShortComplex.moduleCat_exact_iff (clsSCOf C n)).1 (clsSC_exactOf C n) _ hπ
  have hw' : (C.toCycles n (n + 1)).hom w
      = C.cyclesMk z (n + 2) hnext hz - C.cyclesMk z' (n + 2) hnext hz' := hw
  refine ⟨w, ?_⟩
  have h1 : (C.iCycles (n + 1)).hom ((C.toCycles n (n + 1)).hom w)
      = (C.iCycles (n + 1)).hom (C.cyclesMk z (n + 2) hnext hz)
        - (C.iCycles (n + 1)).hom (C.cyclesMk z' (n + 2) hnext hz') := by
    rw [← map_sub]
    exact congrArg (C.iCycles (n + 1)).hom hw'
  have h2 : (C.iCycles (n + 1)).hom (C.cyclesMk z (n + 2) hnext hz) = z :=
    C.i_cyclesMk z (n + 2) hnext hz
  have h3 : (C.iCycles (n + 1)).hom (C.cyclesMk z' (n + 2) hnext hz') = z' :=
    C.i_cyclesMk z' (n + 2) hnext hz'
  have h4 : (C.iCycles (n + 1)).hom ((C.toCycles n (n + 1)).hom w)
      = (C.d n (n + 1)).hom w := by
    rw [← ModuleCat.comp_apply, C.toCycles_i]
  rw [h4, h2, h3] at h1
  rw [h1]
  abel

/-! ## 6. The ambient term is a quotient of the global cochains -/

/-- The restriction of global cochains to the small-chain dual. -/
def ambDualMapOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    cochainCxK K X ⟶ (mvCoSCOf K U V hUV).X₁ :=
  dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))

theorem mvAmbientIsoOf_inv (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvAmbientIsoOf K U V hUV n).inv
      = HomologicalComplex.homologyMap (ambDualMapOf K U V hUV) n := rfl

/-- **The restriction of a global cochain to the small chains is surjective**, over a field. -/
theorem eltAmbOf_surjective (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : (mvCoSCOf K U V hUV).X₁.X n) :
    ∃ c : singularCochainGroup K X n, eltAmbOf K U V hUV n c = x := by
  haveI : Mono ((smallChainsInclusion K X (twoSetCover U V hUV)).f n) :=
    (ModuleCat.mono_iff_injective _).2 (fun a b hab => Subtype.ext hab)
  haveI : Epi ((ambDualMapOf K U V hUV).f n) := by
    show Epi ((cohDualFunctorOf K).map
      (((smallChainsInclusion K X (twoSetCover U V hUV)).f n).op))
    infer_instance
  obtain ⟨c, hc⟩ :=
    (ModuleCat.epi_iff_surjective ((ambDualMapOf K U V hUV).f n)).1 inferInstance x
  exact ⟨c, hc⟩

/-! ## 7. The connecting map on cochain data -/

/-- **The Mayer–Vietoris connecting map over a field, computed on cochains.** -/
theorem mvDeltaOf_spec (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (α : singularCochainGroup K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p)
    (hα : cochainCoboundary K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α = 0)
    (aU : singularCochainGroup K (TopCat.of (U : Set X)) p)
    (aV : singularCochainGroup K (TopCat.of (V : Set X)) p)
    (haUV : cochainPullback (subInclusion Set.inter_subset_left) p aU
        - cochainPullback (subInclusion Set.inter_subset_right) p aV = α)
    (γ : singularCochainGroup K X (p + 1))
    (hγ : cochainCoboundary K X (p + 1) γ = 0)
    (hγU : cochainPullback (sInclusion (U : Set X)) (p + 1) γ
        = cochainCoboundary K (TopCat.of (U : Set X)) p aU)
    (hγV : cochainPullback (sInclusion (V : Set X)) (p + 1) γ
        = cochainCoboundary K (TopCat.of (V : Set X)) p aV) :
    (mvDeltaOf K U V hUV p).hom
        (cocycleClassK K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα)
      = cocycleClassK K X (p + 1) γ hγ := by
  have hx₃ : ((mvCoSCOf K U V hUV).X₃.d p (p + 1)).hom
      (eltSubOf K ((U : Set X) ∩ (V : Set X)) p α) = 0 := by
    show ((dualCxOf K (subChainComplex K X ((U : Set X) ∩ (V : Set X)))).d p (p + 1)).hom
        (eltSubOf K ((U : Set X) ∩ (V : Set X)) p α) = 0
    rw [d_eltSubOf, hα, eltSub_zeroOf]
  have hx₂ : (mvGmidOf K U V hUV p).hom (eltUOf K U V p aU + eltVOf K U V p aV)
      = eltSubOf K ((U : Set X) ∩ (V : Set X)) p α := by
    refine (map_add (mvGmidOf K U V hUV p).hom (eltUOf K U V p aU) (eltVOf K U V p aV)).trans ?_
    rw [mvGmid_eltUOf, mvGmid_eltVOf, ← sub_eq_add_neg, ← eltSub_subOf, haUV]
  have hx₁ : (mvFmidOf K U V hUV (p + 1)).hom (eltAmbOf K U V hUV (p + 1) γ)
      = ((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom
          (eltUOf K U V p aU + eltVOf K U V p aV) := by
    refine mvX2_extOf K U V (p + 1) ?_ ?_
    · rw [projU_mvFmid_eltAmbOf, hγU, projU_dOf, map_add, projU_eltUOf, projU_eltVOf, add_zero]
      exact (d_eltSubOf K (U : Set X) p aU).symm
    · rw [projV_mvFmid_eltAmbOf, hγV, projV_dOf, map_add, projV_eltUOf, projV_eltVOf, zero_add]
      exact (d_eltSubOf K (V : Set X) p aV).symm
  have hδ := delta_applyOf K U V hUV p (eltSubOf K ((U : Set X) ∩ (V : Set X)) p α) hx₃
    (eltUOf K U V p aU + eltVOf K U V p aV) hx₂ (eltAmbOf K U V hUV (p + 1) γ) hx₁
  have hsrc : (mvInterIsoOf K U V hUV p).inv.hom
        (cocycleClassK K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα)
      = cls₃Of K U V hUV p (eltSubOf K ((U : Set X) ∩ (V : Set X)) p α) hx₃ := by
    exact CohClass.homologyMap_clsOfK
      ((subCxDualIsoOf K ((U : Set X) ∩ (V : Set X))).inv) p α hα hx₃
  have htgt : (HomologicalComplex.homologyMap (ambDualMapOf K U V hUV) (p + 1)).hom
        (cocycleClassK K X (p + 1) γ hγ)
      = cls₁Of K U V hUV p (eltAmbOf K U V hUV (p + 1) γ)
          (d_eq_zero_of_descendsOf K U V hUV p _ _ hx₁) := by
    exact CohClass.homologyMap_clsOfK (ambDualMapOf K U V hUV) (p + 1) γ hγ _
  have hchain : (mvDeltaOf K U V hUV p).hom
      (cocycleClassK K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα)
    = (mvAmbientIsoOf K U V hUV (p + 1)).hom.hom
        (cls₁Of K U V hUV p (eltAmbOf K U V hUV (p + 1) γ)
          (d_eq_zero_of_descendsOf K U V hUV p _ _ hx₁)) := by
    show ((mvInterIsoOf K U V hUV p).inv
        ≫ (mvCoSCOf_shortExact K U V hUV).δ p (p + 1) (upRel p)
        ≫ (mvAmbientIsoOf K U V hUV (p + 1)).hom).hom _ = _
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hsrc, hδ]
  rw [hchain, ← htgt]
  have hfin := congrArg (fun ψ => ψ.hom (cocycleClassK K X (p + 1) γ hγ))
    (mvAmbientIsoOf K U V hUV (p + 1)).inv_hom_id
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hfin
  exact hfin

/-! ## 8. The cochain data exists -/

/-- **Every class on `U ∩ V` admits cochain data computing `mvDeltaOf`.** -/
theorem mvDeltaOf_data (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (a : Hmod K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p) :
    ∃ (α : singularCochainGroup K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p)
      (hα : cochainCoboundary K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α = 0)
      (aU : singularCochainGroup K (TopCat.of (U : Set X)) p)
      (aV : singularCochainGroup K (TopCat.of (V : Set X)) p)
      (γ : singularCochainGroup K X (p + 1))
      (_ : cochainCoboundary K X (p + 1) γ = 0),
      cocycleClassK K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα = a
      ∧ cochainPullback (subInclusion Set.inter_subset_left) p aU
          - cochainPullback (subInclusion Set.inter_subset_right) p aV = α
      ∧ cochainPullback (sInclusion (U : Set X)) (p + 1) γ
          = cochainCoboundary K (TopCat.of (U : Set X)) p aU
      ∧ cochainPullback (sInclusion (V : Set X)) (p + 1) γ
          = cochainCoboundary K (TopCat.of (V : Set X)) p aV := by
  obtain ⟨α, hα, hαcls⟩ :=
    CohClass.clsOfK_surjective (cochainCxK K (TopCat.of ↥((U : Set X) ∩ (V : Set X)))) p a
  have hα' : cochainCoboundary K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α = 0 := hα
  have hdα : ((dualCxOf K (subChainComplex K X ((U : Set X) ∩ (V : Set X)))).d p (p + 1)).hom
      (eltSubOf K ((U : Set X) ∩ (V : Set X)) p α) = 0 := by
    rw [d_eltSubOf, hα', eltSub_zeroOf]
  obtain ⟨x₂, hx₂g⟩ : ∃ x₂ : (dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).X p,
      (mvGmidOf K U V hUV p).hom x₂ = eltSubOf K ((U : Set X) ∩ (V : Set X)) p α :=
    ⟨_, mvSectG_gOf K U V hUV p _⟩
  obtain ⟨x₁, hx₁f⟩ : ∃ x₁ : (mvCoSCOf K U V hUV).X₁.X (p + 1),
      (mvFmidOf K U V hUV (p + 1)).hom x₁
        = ((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom x₂ := by
    refine ⟨(mvRetrFOf K U V hUV (p + 1)).hom
      (((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom x₂),
      f_mvRetrFOf K U V hUV (p + 1) _ ?_⟩
    rw [g_dOf, hx₂g]
    exact hdα
  have hx₁d := d_eq_zero_of_descendsOf K U V hUV p x₂ x₁ hx₁f
  obtain ⟨γ, hγ, hγcls⟩ := CohClass.clsOfK_surjective (cochainCxK K X) (p + 1)
    ((mvAmbientIsoOf K U V hUV (p + 1)).hom.hom (cls₁Of K U V hUV p x₁ hx₁d))
  have hγ' : cochainCoboundary K X (p + 1) γ = 0 := hγ
  have heq : CohClass.clsOfK (mvCoSCOf K U V hUV).X₁ (p + 1) (eltAmbOf K U V hUV (p + 1) γ)
        (CohClass.d_map_eq_zeroK (ambDualMapOf K U V hUV) (p + 1) γ hγ)
      = CohClass.clsOfK (mvCoSCOf K U V hUV).X₁ (p + 1) x₁ hx₁d := by
    have h1 := CohClass.homologyMap_clsOfK (ambDualMapOf K U V hUV) (p + 1) γ hγ
      (CohClass.d_map_eq_zeroK (ambDualMapOf K U V hUV) (p + 1) γ hγ)
    refine h1.symm.trans ?_
    rw [hγcls]
    have h2 := congrArg (fun ψ => ψ.hom (cls₁Of K U V hUV p x₁ hx₁d))
      (mvAmbientIsoOf K U V hUV (p + 1)).hom_inv_id
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h2
    exact h2
  obtain ⟨w, hw⟩ := exists_d_of_clsOfK_eq (mvCoSCOf K U V hUV).X₁ p
    (eltAmbOf K U V hUV (p + 1) γ) x₁
    (CohClass.d_map_eq_zeroK (ambDualMapOf K U V hUV) (p + 1) γ hγ) hx₁d heq
  have hx₂' : (mvFmidOf K U V hUV (p + 1)).hom (eltAmbOf K U V hUV (p + 1) γ)
      = ((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom
          (x₂ + (mvFmidOf K U V hUV p).hom w) := by
    have e1 : (mvFmidOf K U V hUV (p + 1)).hom (eltAmbOf K U V hUV (p + 1) γ)
        = ((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom x₂
          + ((dualCxOf K (mvCxOf K U ⊞ mvCxOf K V)).d p (p + 1)).hom
              ((mvFmidOf K U V hUV p).hom w) := by
      rw [hw, map_add, hx₁f, f_dOf]
    rw [e1, ← map_add]
  have hg₂' : (mvGmidOf K U V hUV p).hom (x₂ + (mvFmidOf K U V hUV p).hom w)
      = eltSubOf K ((U : Set X) ∩ (V : Set X)) p α := by
    refine (map_add (mvGmidOf K U V hUV p).hom x₂
      ((mvFmidOf K U V hUV p).hom w)).trans ?_
    rw [hx₂g, g_f_applyOf, add_zero]
  obtain ⟨aU, haU⟩ : ∃ aU : singularCochainGroup K (TopCat.of (U : Set X)) p,
      eltSubOf K (U : Set X) p aU
        = ((mvCxProjUOf K U V).f p).hom (x₂ + (mvFmidOf K U V hUV p).hom w) :=
    ⟨_, eltSub_homOf K (U : Set X) p _⟩
  obtain ⟨aV, haV⟩ : ∃ aV : singularCochainGroup K (TopCat.of (V : Set X)) p,
      eltSubOf K (V : Set X) p aV
        = ((mvCxProjVOf K U V).f p).hom (x₂ + (mvFmidOf K U V hUV p).hom w) :=
    ⟨_, eltSub_homOf K (V : Set X) p _⟩
  have hsplit : eltUOf K U V p aU + eltVOf K U V p aV
      = x₂ + (mvFmidOf K U V hUV p).hom w := by
    refine mvX2_extOf K U V p ?_ ?_
    · rw [map_add, projU_eltUOf, projU_eltVOf, add_zero, haU]
    · rw [map_add, projV_eltUOf, projV_eltVOf, zero_add, haV]
  refine ⟨α, hα', aU, aV, γ, hγ', hαcls, ?_, ?_, ?_⟩
  · refine eltSub_injectiveOf K ((U : Set X) ∩ (V : Set X)) p ?_
    refine (eltSub_subOf K ((U : Set X) ∩ (V : Set X)) p _ _).trans ?_
    rw [← mvGmid_eltUOf K U V hUV p aU, sub_eq_add_neg, ← mvGmid_eltVOf K U V hUV p aV]
    refine (map_add (mvGmidOf K U V hUV p).hom (eltUOf K U V p aU)
      (eltVOf K U V p aV)).symm.trans ?_
    rw [hsplit, hg₂']
  · refine eltSub_injectiveOf K (U : Set X) (p + 1) ?_
    rw [← projU_mvFmid_eltAmbOf K U V hUV (p + 1) γ, hx₂', projU_dOf, ← hsplit, map_add,
      projU_eltUOf, projU_eltVOf, add_zero]
    exact d_eltSubOf K (U : Set X) p aU
  · refine eltSub_injectiveOf K (V : Set X) (p + 1) ?_
    rw [← projV_mvFmid_eltAmbOf K U V hUV (p + 1) γ, hx₂', projV_dOf, ← hsplit, map_add,
      projV_eltUOf, projV_eltVOf, zero_add]
    exact d_eltSubOf K (V : Set X) p aV

end MVDelta

end

end GroupApproximation.CharClass
