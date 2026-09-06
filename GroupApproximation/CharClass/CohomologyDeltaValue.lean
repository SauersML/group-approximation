import GroupApproximation.CharClass.CohomologyDeltaSpec

/-!
# The Mayer–Vietoris connecting map, evaluated on cochains

`CohomologyDeltaSpec.lean` computes the two maps of the dualized Mayer–Vietoris
sequence on cochains.  This file turns that into a statement about `mvDelta`
itself and produces, for an arbitrary class on `U ∩ V`, cochain data computing
its image.

The subtle point is the ambient term `X₁`, the dual of the **small**-chain
complex.  A cochain on `X` restricts to it, and that restriction is surjective
(`F₂` is injective over itself, so the dual of a degreewise monomorphism is a
degreewise epimorphism), but a class of `X₁` is *not* the restriction of a global
cocycle on the nose: only up to a coboundary.  So the existence statement first
picks a global cocycle representing the value of `mvDelta` and then corrects the
lift of `α` by the resulting coboundary; the correction changes `α`'s two pieces
but not `α`, because it lands in the image of `f`, which `g` kills.

## Main declarations

* `MVDelta.exists_d_of_clsOf_eq` — cocycles with the same class differ by a
  coboundary (a general fact about cochain complexes of `F₂`-modules).
* `MVDelta.eltAmb_surjective` — every element of the ambient term is the
  restriction of a global cochain.
* `MVDelta.mvDelta_spec` — `δ [α] = [γ]` from the cochain data.
* `MVDelta.mvDelta_data` — the cochain data exists for every class.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X : TopCat.{0}}

/-! ## 1. Bookkeeping for `eltSub` -/

theorem eltSub_zero (S : Set X) (p : ℕ) : eltSub S p 0 = 0 := map_zero _

theorem eltSub_add (S : Set X) (p : ℕ)
    (a b : singularCochainGroup (ZMod 2) (TopCat.of S) p) :
    eltSub S p (a + b) = eltSub S p a + eltSub S p b := map_add _ _ _

/-- `eltSub` undoes the identification `subCxDualIso`. -/
theorem eltSub_hom (S : Set X) (p : ℕ)
    (z : (dualCx2 (subChainComplex (ZMod 2) X S)).X p) :
    eltSub S p ((((subCxDualIso S).hom).f p).hom z) = z := by
  rw [eltSub, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    (subCxDualIso S).hom_inv_id, HomologicalComplex.id_f]
  rfl

/-! ## 2. The three maps commute with the differential -/

theorem projU_d (U V : Opens X) (p : ℕ) (z : (dualCx2 (mvCx U ⊞ mvCx V)).X p) :
    ((mvCxProjU U V).f (p + 1)).hom
        (((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom z)
      = ((dualCx2 (mvCx U)).d p (p + 1)).hom (((mvCxProjU U V).f p).hom z) := by
  have h := congrArg (fun ψ => ψ.hom z) ((mvCxProjU U V).comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem projV_d (U V : Opens X) (p : ℕ) (z : (dualCx2 (mvCx U ⊞ mvCx V)).X p) :
    ((mvCxProjV U V).f (p + 1)).hom
        (((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom z)
      = ((dualCx2 (mvCx V)).d p (p + 1)).hom (((mvCxProjV U V).f p).hom z) := by
  have h := congrArg (fun ψ => ψ.hom z) ((mvCxProjV U V).comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

/-! ### The two outer maps, retyped at the explicit biproduct dual

`(mvCoSC U V hUV).X₂` is *definitionally* `dualCx2 (mvCx U ⊞ mvCx V)`, but the
unfolding is semireducible, so instance search and `rw` do not see through it.
Every element of the middle term below is written at the explicit form; these two
maps and the six restatements carry the conversion once and for all. -/

/-- The second map of the dual sequence, with its source written explicitly. -/
def mvGmid (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (dualCx2 (mvCx U ⊞ mvCx V)).X p ⟶ (dualCx2 (subChainComplex (ZMod 2) X ((U : Set X) ∩ (V : Set X)))).X p :=
  (mvCoSC U V hUV).g.f p

/-- The first map of the dual sequence, with its target written explicitly. -/
def mvFmid (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (mvCoSC U V hUV).X₁.X p ⟶ (dualCx2 (mvCx U ⊞ mvCx V)).X p :=
  (mvCoSC U V hUV).f.f p

theorem mvGmid_eltU (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p) :
    (mvGmid U V hUV p).hom (eltU U V p aU)
      = eltSub ((U : Set X) ∩ (V : Set X)) p
          (cochainPullback (subInclusion Set.inter_subset_left) p aU) :=
  g_eltU U V hUV p aU

theorem mvGmid_eltV (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p) :
    (mvGmid U V hUV p).hom (eltV U V p aV)
      = eltSub ((U : Set X) ∩ (V : Set X)) p
          (cochainPullback (subInclusion Set.inter_subset_right) p aV) :=
  g_eltV U V hUV p aV

theorem projU_mvFmid_eltAmb (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (c : singularCochainGroup (ZMod 2) X p) :
    ((mvCxProjU U V).f p).hom ((mvFmid U V hUV p).hom (eltAmb U V hUV p c))
      = eltSub (U : Set X) p (cochainPullback (sInclusion (U : Set X)) p c) :=
  projU_f_eltAmb U V hUV p c

theorem projV_mvFmid_eltAmb (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (c : singularCochainGroup (ZMod 2) X p) :
    ((mvCxProjV U V).f p).hom ((mvFmid U V hUV p).hom (eltAmb U V hUV p c))
      = eltSub (V : Set X) p (cochainPullback (sInclusion (V : Set X)) p c) :=
  projV_f_eltAmb U V hUV p c

theorem g_d (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (z : (dualCx2 (mvCx U ⊞ mvCx V)).X p) :
    (mvGmid U V hUV (p + 1)).hom (((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom z)
      = ((dualCx2 (subChainComplex (ZMod 2) X ((U : Set X) ∩ (V : Set X)))).d p (p + 1)).hom ((mvGmid U V hUV p).hom z) := by
  have h := congrArg (fun ψ => ψ.hom z) ((mvCoSC U V hUV).g.comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem f_d (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) (w : (mvCoSC U V hUV).X₁.X p) :
    (mvFmid U V hUV (p + 1)).hom (((mvCoSC U V hUV).X₁.d p (p + 1)).hom w)
      = ((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom ((mvFmid U V hUV p).hom w) := by
  have h := congrArg (fun ψ => ψ.hom w) ((mvCoSC U V hUV).f.comm p (p + 1))
  simp only [ModuleCat.comp_apply] at h
  exact h.symm

theorem g_f_apply (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (w : (mvCoSC U V hUV).X₁.X p) :
    (mvGmid U V hUV p).hom ((mvFmid U V hUV p).hom w) = 0 := by
  have h : (mvCoSC U V hUV).f.f p ≫ (mvCoSC U V hUV).g.f p
      = (0 : (mvCoSC U V hUV).X₁.X p ⟶ (mvCoSC U V hUV).X₃.X p) := by
    rw [← HomologicalComplex.comp_f, (mvCoSC U V hUV).zero, HomologicalComplex.zero_f]
  have h2 := congrArg (fun ψ => ψ.hom w) h
  simp only [ModuleCat.comp_apply] at h2
  exact h2

/-! ## 3. The splitting: a section of `g` and a retraction of `f` -/

/-- A degreewise section of the second map of the dual sequence. -/
def mvSectG (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (dualCx2 (subChainComplex (ZMod 2) X ((U : Set X) ∩ (V : Set X)))).X p ⟶ (dualCx2 (mvCx U ⊞ mvCx V)).X p :=
  (mvCoSplitting U V hUV p).s

/-- A degreewise retraction of the first map of the dual sequence. -/
def mvRetrF (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ) :
    (dualCx2 (mvCx U ⊞ mvCx V)).X p ⟶ (mvCoSC U V hUV).X₁.X p :=
  (mvCoSplitting U V hUV p).r

theorem mvSectG_g (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (y : (dualCx2 (subChainComplex (ZMod 2) X ((U : Set X) ∩ (V : Set X)))).X p) :
    (mvGmid U V hUV p).hom ((mvSectG U V hUV p).hom y) = y := by
  have h := congrArg (fun ψ => ψ.hom y) (mvCoSplitting U V hUV p).s_g
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h
  exact h

/-- **Every element killed by `g` is in the image of `f`**, with an explicit
preimage given by the splitting. -/
theorem f_mvRetrF (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (z : (dualCx2 (mvCx U ⊞ mvCx V)).X p) (hz : (mvGmid U V hUV p).hom z = 0) :
    (mvFmid U V hUV p).hom ((mvRetrF U V hUV p).hom z) = z := by
  have h := congrArg (fun ψ => ψ.hom z) (mvCoSplitting U V hUV p).id
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at h
  have h2 : (mvFmid U V hUV p).hom ((mvRetrF U V hUV p).hom z)
      + ((mvSectG U V hUV p).hom ((mvGmid U V hUV p).hom z)) = z := h
  rw [hz, map_zero, add_zero] at h2
  exact h2

/-! ## 4. Cocycles with the same class differ by a coboundary -/

/-- The short complex `K^n → Z^{n+1} → H^{n+1}` of a cochain complex. -/
def clsSC (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (n : ℕ) :
    ShortComplex (ModuleCat.{0} (ZMod 2)) :=
  ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ n (n + 1))

theorem clsSC_exact (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (n : ℕ) :
    (clsSC K n).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (K.homologyIsCokernel n (n + 1) (ComplexShape.prev_eq' _ (upRel n)))

/-- **Two cocycles with the same class differ by a coboundary.** -/
theorem exists_d_of_clsOf_eq (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (n : ℕ)
    (z z' : K.X (n + 1))
    (hz : (K.d (n + 1) (n + 2)).hom z = 0) (hz' : (K.d (n + 1) (n + 2)).hom z' = 0)
    (h : CohClass.clsOf K (n + 1) z hz = CohClass.clsOf K (n + 1) z' hz') :
    ∃ w : K.X n, z = z' + (K.d n (n + 1)).hom w := by
  have hnext : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
    ComplexShape.next_eq' _ (upRel (n + 1))
  have hπ : ((clsSC K n).g).hom
      (K.cyclesMk z (n + 2) hnext hz - K.cyclesMk z' (n + 2) hnext hz') = 0 := by
    refine (map_sub ((clsSC K n).g).hom (K.cyclesMk z (n + 2) hnext hz)
      (K.cyclesMk z' (n + 2) hnext hz')).trans ?_
    exact sub_eq_zero_of_eq h
  obtain ⟨w, hw⟩ :=
    (ShortComplex.moduleCat_exact_iff (clsSC K n)).1 (clsSC_exact K n) _ hπ
  have hw' : (K.toCycles n (n + 1)).hom w
      = K.cyclesMk z (n + 2) hnext hz - K.cyclesMk z' (n + 2) hnext hz' := hw
  refine ⟨w, ?_⟩
  have h1 : (K.iCycles (n + 1)).hom ((K.toCycles n (n + 1)).hom w)
      = (K.iCycles (n + 1)).hom (K.cyclesMk z (n + 2) hnext hz)
        - (K.iCycles (n + 1)).hom (K.cyclesMk z' (n + 2) hnext hz') := by
    rw [← map_sub]
    exact congrArg (K.iCycles (n + 1)).hom hw'
  have h2 : (K.iCycles (n + 1)).hom (K.cyclesMk z (n + 2) hnext hz) = z :=
    K.i_cyclesMk z (n + 2) hnext hz
  have h3 : (K.iCycles (n + 1)).hom (K.cyclesMk z' (n + 2) hnext hz') = z' :=
    K.i_cyclesMk z' (n + 2) hnext hz'
  have h4 : (K.iCycles (n + 1)).hom ((K.toCycles n (n + 1)).hom w)
      = (K.d n (n + 1)).hom w := by
    rw [← ModuleCat.comp_apply, K.toCycles_i]
  rw [h4, h2, h3] at h1
  rw [h1]
  abel

/-! ## 5. The ambient term is a quotient of the global cochains -/

/-- The restriction of global cochains to the small-chain dual, with its source
written as the singular cochain complex of `X`. -/
def ambDualMap (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    cochainCxZMod2 X ⟶ (mvCoSC U V hUV).X₁ :=
  dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))

theorem eltAmb_eq (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (c : singularCochainGroup (ZMod 2) X p) :
    eltAmb U V hUV p c = ((ambDualMap U V hUV).f p).hom c := rfl

theorem mvAmbientIso_inv (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvAmbientIso U V hUV n).inv
      = HomologicalComplex.homologyMap (ambDualMap U V hUV) n := rfl

/-- **The restriction of a global cochain to the small chains is surjective.** -/
theorem eltAmb_surjective (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : (mvCoSC U V hUV).X₁.X n) :
    ∃ c : singularCochainGroup (ZMod 2) X n, eltAmb U V hUV n c = x := by
  haveI : Mono ((smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV)).f n) :=
    (ModuleCat.mono_iff_injective _).2 (fun a b hab => Subtype.ext hab)
  haveI : Epi ((ambDualMap U V hUV).f n) := by
    show Epi (cohDualFunctor.map
      (((smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV)).f n).op))
    infer_instance
  obtain ⟨c, hc⟩ :=
    (ModuleCat.epi_iff_surjective ((ambDualMap U V hUV).f n)).1 inferInstance x
  exact ⟨c, hc⟩

/-! ## 6. The connecting map on cochain data -/

/-- **The Mayer–Vietoris connecting map, computed on cochains.** -/
theorem mvDelta_spec (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (α : singularCochainGroup (ZMod 2)
      (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p)
    (hα : cochainCoboundary (ZMod 2)
      (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α = 0)
    (aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p)
    (aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p)
    (haUV : cochainPullback (subInclusion Set.inter_subset_left) p aU
        + cochainPullback (subInclusion Set.inter_subset_right) p aV = α)
    (γ : singularCochainGroup (ZMod 2) X (p + 1))
    (hγ : cochainCoboundary (ZMod 2) X (p + 1) γ = 0)
    (hγU : cochainPullback (sInclusion (U : Set X)) (p + 1) γ
        = cochainCoboundary (ZMod 2) (TopCat.of (U : Set X)) p aU)
    (hγV : cochainPullback (sInclusion (V : Set X)) (p + 1) γ
        = cochainCoboundary (ZMod 2) (TopCat.of (V : Set X)) p aV) :
    (mvDelta U V hUV p).hom
        (cocycleClass (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα)
      = cocycleClass X (p + 1) γ hγ := by
  have hx₃ : ((mvCoSC U V hUV).X₃.d p (p + 1)).hom
      (eltSub ((U : Set X) ∩ (V : Set X)) p α) = 0 := by
    show ((dualCx2 (subChainComplex (ZMod 2) X ((U : Set X) ∩ (V : Set X)))).d p (p + 1)).hom
        (eltSub ((U : Set X) ∩ (V : Set X)) p α) = 0
    rw [d_eltSub, hα, eltSub_zero]
  have hx₂ : (mvGmid U V hUV p).hom (eltU U V p aU + eltV U V p aV)
      = eltSub ((U : Set X) ∩ (V : Set X)) p α := by
    refine (map_add (mvGmid U V hUV p).hom (eltU U V p aU) (eltV U V p aV)).trans ?_
    rw [mvGmid_eltU, mvGmid_eltV, ← eltSub_add, haUV]
  have hx₁ : (mvFmid U V hUV (p + 1)).hom (eltAmb U V hUV (p + 1) γ)
      = ((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom
          (eltU U V p aU + eltV U V p aV) := by
    refine mvX2_ext U V (p + 1) ?_ ?_
    · rw [projU_mvFmid_eltAmb, hγU, projU_d, map_add, projU_eltU, projU_eltV, add_zero]
      exact (d_eltSub (U : Set X) p aU).symm
    · rw [projV_mvFmid_eltAmb, hγV, projV_d, map_add, projV_eltU, projV_eltV, zero_add]
      exact (d_eltSub (V : Set X) p aV).symm
  have hδ := delta_apply U V hUV p (eltSub ((U : Set X) ∩ (V : Set X)) p α) hx₃
    (eltU U V p aU + eltV U V p aV) hx₂ (eltAmb U V hUV (p + 1) γ) hx₁
  have hsrc : (mvInterIso U V hUV p).inv.hom
        (cocycleClass (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα)
      = cls₃ U V hUV p (eltSub ((U : Set X) ∩ (V : Set X)) p α) hx₃ := by
    exact CohClass.homologyMap_clsOf
      ((subCxDualIso ((U : Set X) ∩ (V : Set X))).inv) p α hα hx₃
  have htgt : (HomologicalComplex.homologyMap (ambDualMap U V hUV) (p + 1)).hom
        (cocycleClass X (p + 1) γ hγ)
      = cls₁ U V hUV p (eltAmb U V hUV (p + 1) γ)
          (d_eq_zero_of_descends U V hUV p _ _ hx₁) := by
    exact CohClass.homologyMap_clsOf (ambDualMap U V hUV) (p + 1) γ hγ _
  have hchain : (mvDelta U V hUV p).hom
      (cocycleClass (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα)
    = (mvAmbientIso U V hUV (p + 1)).hom.hom
        (cls₁ U V hUV p (eltAmb U V hUV (p + 1) γ)
          (d_eq_zero_of_descends U V hUV p _ _ hx₁)) := by
    show ((mvInterIso U V hUV p).inv
        ≫ (mvCoSC_shortExact U V hUV).δ p (p + 1) (upRel p)
        ≫ (mvAmbientIso U V hUV (p + 1)).hom).hom _ = _
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hsrc, hδ]
  rw [hchain, ← htgt]
  have hfin := congrArg (fun ψ => ψ.hom (cocycleClass X (p + 1) γ hγ))
    (mvAmbientIso U V hUV (p + 1)).inv_hom_id
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hfin
  exact hfin

/-! ## 7. The cochain data exists -/

/-- **Every class on `U ∩ V` admits cochain data computing `mvDelta`.** -/
theorem mvDelta_data (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (a : Hmod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p) :
    ∃ (α : singularCochainGroup (ZMod 2)
          (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p)
      (hα : cochainCoboundary (ZMod 2)
          (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α = 0)
      (aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p)
      (aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p)
      (γ : singularCochainGroup (ZMod 2) X (p + 1))
      (_ : cochainCoboundary (ZMod 2) X (p + 1) γ = 0),
      cocycleClass (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α hα = a
      ∧ cochainPullback (subInclusion Set.inter_subset_left) p aU
          + cochainPullback (subInclusion Set.inter_subset_right) p aV = α
      ∧ cochainPullback (sInclusion (U : Set X)) (p + 1) γ
          = cochainCoboundary (ZMod 2) (TopCat.of (U : Set X)) p aU
      ∧ cochainPullback (sInclusion (V : Set X)) (p + 1) γ
          = cochainCoboundary (ZMod 2) (TopCat.of (V : Set X)) p aV := by
  obtain ⟨α, hα, hαcls⟩ :=
    CohClass.clsOf_surjective
      (cochainCxZMod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X)))) p a
  have hα' : cochainCoboundary (ZMod 2)
      (TopCat.of ↥((U : Set X) ∩ (V : Set X))) p α = 0 := hα
  have hdα : ((dualCx2 (subChainComplex (ZMod 2) X ((U : Set X) ∩ (V : Set X)))).d p (p + 1)).hom
      (eltSub ((U : Set X) ∩ (V : Set X)) p α) = 0 := by
    rw [d_eltSub, hα', eltSub_zero]
  obtain ⟨x₂, hx₂g⟩ : ∃ x₂ : (dualCx2 (mvCx U ⊞ mvCx V)).X p,
      (mvGmid U V hUV p).hom x₂
        = eltSub ((U : Set X) ∩ (V : Set X)) p α :=
    ⟨_, mvSectG_g U V hUV p _⟩
  obtain ⟨x₁, hx₁f⟩ : ∃ x₁ : (mvCoSC U V hUV).X₁.X (p + 1),
      (mvFmid U V hUV (p + 1)).hom x₁
        = ((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom x₂ := by
    refine ⟨(mvRetrF U V hUV (p + 1)).hom
      (((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom x₂), f_mvRetrF U V hUV (p + 1) _ ?_⟩
    rw [g_d, hx₂g]
    exact hdα
  have hx₁d := d_eq_zero_of_descends U V hUV p x₂ x₁ hx₁f
  obtain ⟨γ, hγ, hγcls⟩ := CohClass.clsOf_surjective (cochainCxZMod2 X) (p + 1)
    ((mvAmbientIso U V hUV (p + 1)).hom.hom (cls₁ U V hUV p x₁ hx₁d))
  have hγ' : cochainCoboundary (ZMod 2) X (p + 1) γ = 0 := hγ
  have heq : CohClass.clsOf (mvCoSC U V hUV).X₁ (p + 1) (eltAmb U V hUV (p + 1) γ)
        (CohClass.d_map_eq_zero (ambDualMap U V hUV) (p + 1) γ hγ)
      = CohClass.clsOf (mvCoSC U V hUV).X₁ (p + 1) x₁ hx₁d := by
    have h1 := CohClass.homologyMap_clsOf (ambDualMap U V hUV) (p + 1) γ hγ
      (CohClass.d_map_eq_zero (ambDualMap U V hUV) (p + 1) γ hγ)
    refine h1.symm.trans ?_
    rw [hγcls]
    have h2 := congrArg (fun ψ => ψ.hom (cls₁ U V hUV p x₁ hx₁d))
      (mvAmbientIso U V hUV (p + 1)).hom_inv_id
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h2
    exact h2
  obtain ⟨w, hw⟩ := exists_d_of_clsOf_eq (mvCoSC U V hUV).X₁ p
    (eltAmb U V hUV (p + 1) γ) x₁
    (CohClass.d_map_eq_zero (ambDualMap U V hUV) (p + 1) γ hγ) hx₁d heq
  have hx₂' : (mvFmid U V hUV (p + 1)).hom (eltAmb U V hUV (p + 1) γ)
      = ((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom
          (x₂ + (mvFmid U V hUV p).hom w) := by
    have e1 : (mvFmid U V hUV (p + 1)).hom (eltAmb U V hUV (p + 1) γ)
        = ((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom x₂
          + ((dualCx2 (mvCx U ⊞ mvCx V)).d p (p + 1)).hom
              ((mvFmid U V hUV p).hom w) := by
      rw [hw, map_add, hx₁f, f_d]
    rw [e1, ← map_add]
  have hg₂' : (mvGmid U V hUV p).hom (x₂ + (mvFmid U V hUV p).hom w)
      = eltSub ((U : Set X) ∩ (V : Set X)) p α := by
    refine (map_add (mvGmid U V hUV p).hom x₂
      ((mvFmid U V hUV p).hom w)).trans ?_
    rw [hx₂g, g_f_apply, add_zero]
  obtain ⟨aU, haU⟩ : ∃ aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p,
      eltSub (U : Set X) p aU
        = ((mvCxProjU U V).f p).hom (x₂ + (mvFmid U V hUV p).hom w) :=
    ⟨_, eltSub_hom (U : Set X) p _⟩
  obtain ⟨aV, haV⟩ : ∃ aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p,
      eltSub (V : Set X) p aV
        = ((mvCxProjV U V).f p).hom (x₂ + (mvFmid U V hUV p).hom w) :=
    ⟨_, eltSub_hom (V : Set X) p _⟩
  have hsplit : eltU U V p aU + eltV U V p aV
      = x₂ + (mvFmid U V hUV p).hom w := by
    refine mvX2_ext U V p ?_ ?_
    · rw [map_add, projU_eltU, projU_eltV, add_zero, haU]
    · rw [map_add, projV_eltU, projV_eltV, zero_add, haV]
  refine ⟨α, hα', aU, aV, γ, hγ', hαcls, ?_, ?_, ?_⟩
  · refine eltSub_injective ((U : Set X) ∩ (V : Set X)) p ?_
    refine (eltSub_add ((U : Set X) ∩ (V : Set X)) p _ _).trans ?_
    rw [← mvGmid_eltU U V hUV p aU, ← mvGmid_eltV U V hUV p aV]
    refine (map_add (mvGmid U V hUV p).hom (eltU U V p aU)
      (eltV U V p aV)).symm.trans ?_
    rw [hsplit, hg₂']
  · refine eltSub_injective (U : Set X) (p + 1) ?_
    rw [← projU_mvFmid_eltAmb U V hUV (p + 1) γ, hx₂', projU_d, ← hsplit, map_add,
      projU_eltU, projU_eltV, add_zero]
    exact d_eltSub (U : Set X) p aU
  · refine eltSub_injective (V : Set X) (p + 1) ?_
    rw [← projV_mvFmid_eltAmb U V hUV (p + 1) γ, hx₂', projV_d, ← hsplit, map_add,
      projV_eltU, projV_eltV, zero_add]
    exact d_eltSub (V : Set X) p aV

end MVDelta

end

end GroupApproximation.CharClass
