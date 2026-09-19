import GroupApproximation.CharClass.CohomologyDeltaChain

/-!
# The Mayer–Vietoris connecting map, computed on cochains

This is the cochain characterisation of `mvDelta`: given a cocycle `α` on `U ∩ V`,
cochains `α_U` and `α_V` on the two pieces whose restrictions add up to `α`, and a
cochain `γ` on the ambient space restricting to `d α_U` on `U` and to `d α_V` on
`V`, the connecting map takes the class of `α` to the class of `γ`.

Everything is assembled from `MVDelta.delta_apply` (any lift along `g` and any
descent along `f` compute `δ`), `CohClass.clsOf` and its naturality (the terms of
the sequence are duals of subordinate-chain complexes, not cochain complexes of
spaces), and the chain-level identification of the two maps of the sequence.

The choice that keeps this small is the descent: `x₁` is taken to be the
restriction of the global cochain `γ` from the start, so no cup product on the
dual of the small-chain complex is ever needed.

## Main declarations

* `MVDelta.eltSub`, `MVDelta.eltU`, `MVDelta.eltV`, `MVDelta.eltAmb` — cochains as
  elements of the three terms.
* `MVDelta.g_eltU`, `MVDelta.g_eltV` — the second map on them.
* `MVDelta.projU_f_eltAmb`, `MVDelta.projV_f_eltAmb` — the first map, followed by
  either component projection, on the restriction of a global cochain.

`MVDelta.mvDelta_spec`, the characterisation these feed, is in
`CohomologyDeltaValue.lean`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X : TopCat.{0}}

/-! ## 1. Cochains as elements of the terms of the sequence -/

/-- A cochain on the subspace `S`, as an element of the dual of the subordinate
chains of `S`. -/
def eltSub (S : Set X) (p : ℕ) (a : singularCochainGroup (ZMod 2) (TopCat.of S) p) :
    (dualCx2 (subChainComplex (ZMod 2) X S)).X p :=
  (((subCxDualIso S).inv).f p).hom a

/-- The identification `subCxDualIso` undoes `eltSub`. -/
@[simp] theorem hom_eltSub (S : Set X) (p : ℕ)
    (a : singularCochainGroup (ZMod 2) (TopCat.of S) p) :
    (((subCxDualIso S).hom).f p).hom (eltSub S p a) = a := by
  rw [eltSub, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    (subCxDualIso S).inv_hom_id, HomologicalComplex.id_f]
  rfl

/-- The same, written with `dualMap2` rather than `subCxDualIso`, which is the form
that comes out of the chain-level identities. -/
@[simp] theorem dualMap2_corestrict_eltSub (S : Set X) (p : ℕ)
    (a : singularCochainGroup (ZMod 2) (TopCat.of S) p) :
    ((dualMap2 (subChainCorestrict (ZMod 2) X S)).f p).hom (eltSub S p a) = a :=
  hom_eltSub S p a

theorem eltSub_injective (S : Set X) (p : ℕ) {a b : singularCochainGroup (ZMod 2)
    (TopCat.of S) p} (h : eltSub S p a = eltSub S p b) : a = b := by
  have := congrArg (((subCxDualIso S).hom).f p).hom h
  rwa [hom_eltSub, hom_eltSub] at this

/-- Two elements of the dual of the subordinate chains agree once their images under
`subCxDualIso` do. -/
theorem eltSub_ext (S : Set X) (p : ℕ) {z w : (dualCx2 (subChainComplex (ZMod 2) X S)).X p}
    (h : (((subCxDualIso S).hom).f p).hom z = (((subCxDualIso S).hom).f p).hom w) :
    z = w :=
  (ModuleCat.mono_iff_injective (((subCxDualIso S).hom).f p)).1 inferInstance h

/-- `eltSub` is a cochain map: it commutes with the coboundary. -/
theorem d_eltSub (S : Set X) (p : ℕ) (a : singularCochainGroup (ZMod 2) (TopCat.of S) p) :
    ((dualCx2 (subChainComplex (ZMod 2) X S)).d p (p + 1)).hom (eltSub S p a)
      = eltSub S (p + 1) (cochainCoboundary (ZMod 2) (TopCat.of S) p a) := by
  have hcomm := ((subCxDualIso S).inv).comm p (p + 1)
  have h := congrArg (fun ψ => ψ.hom a) hcomm
  simp only [ModuleCat.comp_apply] at h
  exact h

/-- A cochain on `U`, as an element of the middle term. -/
def eltU (U V : Opens X) (p : ℕ)
    (aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p) :
    (dualCx2 (mvCx U ⊞ mvCx V)).X p :=
  ((mvCxInclU U V).f p).hom (eltSub (U : Set X) p aU)

/-- A cochain on `V`, as an element of the middle term. -/
def eltV (U V : Opens X) (p : ℕ)
    (aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p) :
    (dualCx2 (mvCx U ⊞ mvCx V)).X p :=
  ((mvCxInclV U V).f p).hom (eltSub (V : Set X) p aV)

/-- A cochain on the ambient space, as an element of the first term. -/
def eltAmb (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (c : singularCochainGroup (ZMod 2) X p) : (mvCoSC U V hUV).X₁.X p :=
  ((dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))).f p).hom c

/-! ## 2. The second map of the sequence on those elements -/

theorem g_eltU (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p) :
    (((mvCoSC U V hUV).g).f p).hom (eltU U V p aU)
      = eltSub ((U : Set X) ∩ (V : Set X)) p
          (cochainPullback (subInclusion Set.inter_subset_left) p aU) := by
  have hcx : (mvCxInclU U V ≫ (mvCoSC U V hUV).g)
        ≫ dualMap2 (subChainCorestrict (ZMod 2) X ((U : Set X) ∩ (V : Set X)))
      = dualMap2 (subChainCorestrict (ZMod 2) X (U : Set X))
        ≫ dualMap2 (chainCxFun.map (subInclusion Set.inter_subset_left)) := by
    rw [mvCxInclU_comp_g]
    exact dualMap2_subChainCorestrict_naturality Set.inter_subset_left
  refine eltSub_ext _ p ?_
  rw [hom_eltSub]
  have h := congrArg (fun φ => ((φ.f p).hom (eltSub (U : Set X) p aU))) hcx
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    dualMap2_corestrict_eltSub] at h
  exact h

theorem g_eltV (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p) :
    (((mvCoSC U V hUV).g).f p).hom (eltV U V p aV)
      = eltSub ((U : Set X) ∩ (V : Set X)) p
          (cochainPullback (subInclusion Set.inter_subset_right) p aV) := by
  have hcx : (mvCxInclV U V ≫ (mvCoSC U V hUV).g)
        ≫ dualMap2 (subChainCorestrict (ZMod 2) X ((U : Set X) ∩ (V : Set X)))
      = dualMap2 (subChainCorestrict (ZMod 2) X (V : Set X))
        ≫ dualMap2 (chainCxFun.map (subInclusion Set.inter_subset_right)) := by
    rw [mvCxInclV_comp_g]
    exact dualMap2_subChainCorestrict_naturality Set.inter_subset_right
  refine eltSub_ext _ p ?_
  rw [hom_eltSub]
  have h := congrArg (fun φ => ((φ.f p).hom (eltSub (V : Set X) p aV))) hcx
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    dualMap2_corestrict_eltSub] at h
  exact h

/-! ## 3. The first map of the sequence on the ambient cochain -/

/-- Two elements of the middle term agree once their two components do. -/
theorem mvX2_ext (U V : Opens X) (p : ℕ) {z w : (dualCx2 (mvCx U ⊞ mvCx V)).X p}
    (hU : ((mvCxProjU U V).f p).hom z = ((mvCxProjU U V).f p).hom w)
    (hV : ((mvCxProjV U V).f p).hom z = ((mvCxProjV U V).f p).hom w) : z = w := by
  have htot := congrArg (fun φ : (dualCx2 (mvCx U ⊞ mvCx V)) ⟶ (dualCx2 (mvCx U ⊞ mvCx V)) =>
    ((φ.f p).hom z, (φ.f p).hom w)) (mvCx_total U V)
  simp only [Prod.mk.injEq] at htot
  have hz : z = ((mvCxInclU U V).f p).hom (((mvCxProjU U V).f p).hom z)
      + ((mvCxInclV U V).f p).hom (((mvCxProjV U V).f p).hom z) := by
    have := htot.1
    simpa [ModuleCat.comp_apply] using this.symm
  have hw : w = ((mvCxInclU U V).f p).hom (((mvCxProjU U V).f p).hom w)
      + ((mvCxInclV U V).f p).hom (((mvCxProjV U V).f p).hom w) := by
    have := htot.2
    simpa [ModuleCat.comp_apply] using this.symm
  rw [hz, hw, hU, hV]

theorem projU_eltU (U V : Opens X) (p : ℕ)
    (aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p) :
    ((mvCxProjU U V).f p).hom (eltU U V p aU) = eltSub (U : Set X) p aU := by
  rw [eltU, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclU_projU,
    HomologicalComplex.id_f]
  rfl

theorem projU_eltV (U V : Opens X) (p : ℕ)
    (aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p) :
    ((mvCxProjU U V).f p).hom (eltV U V p aV) = 0 := by
  rw [eltV, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclV_projU]
  rfl

theorem projV_eltV (U V : Opens X) (p : ℕ)
    (aV : singularCochainGroup (ZMod 2) (TopCat.of (V : Set X)) p) :
    ((mvCxProjV U V).f p).hom (eltV U V p aV) = eltSub (V : Set X) p aV := by
  rw [eltV, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclV_projV,
    HomologicalComplex.id_f]
  rfl

theorem projV_eltU (U V : Opens X) (p : ℕ)
    (aU : singularCochainGroup (ZMod 2) (TopCat.of (U : Set X)) p) :
    ((mvCxProjV U V).f p).hom (eltU U V p aU) = 0 := by
  rw [eltU, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, mvCxInclU_projV]
  rfl

theorem projU_f_eltAmb (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (c : singularCochainGroup (ZMod 2) X p) :
    ((mvCxProjU U V).f p).hom ((((mvCoSC U V hUV).f).f p).hom (eltAmb U V hUV p c))
      = eltSub (U : Set X) p (cochainPullback (sInclusion (U : Set X)) p c) := by
  have hA := congrArg (fun φ => ((φ.f p).hom (eltAmb U V hUV p c)))
    (f_comp_projU U V hUV)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hA
  have hcx : dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))
        ≫ dualMap2 (mvInclU_small (ZMod 2) U V hUV)
        ≫ dualMap2 (subChainCorestrict (ZMod 2) X (U : Set X))
      = dualMap2 (chainCxFun.map (sInclusion (U : Set X))) := by
    rw [← Category.assoc, mvDualMap_comp, mvDualMap_comp]
    exact congrArg (fun φ => dualMap2 φ) (corestrict_comp_subToAllU U V hUV)
  refine eltSub_ext _ p ?_
  rw [hom_eltSub]
  have h := congrArg (fun φ => ((φ.f p).hom c)) hcx
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  exact (congrArg ((subCxDualIso ((U : Opens X) : Set X)).hom.f p).hom hA).trans h

theorem projV_f_eltAmb (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (c : singularCochainGroup (ZMod 2) X p) :
    ((mvCxProjV U V).f p).hom ((((mvCoSC U V hUV).f).f p).hom (eltAmb U V hUV p c))
      = eltSub (V : Set X) p (cochainPullback (sInclusion (V : Set X)) p c) := by
  have hA := congrArg (fun φ => ((φ.f p).hom (eltAmb U V hUV p c)))
    (f_comp_projV U V hUV)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hA
  have hcx : dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))
        ≫ dualMap2 (mvInclV_small (ZMod 2) U V hUV)
        ≫ dualMap2 (subChainCorestrict (ZMod 2) X (V : Set X))
      = dualMap2 (chainCxFun.map (sInclusion (V : Set X))) := by
    rw [← Category.assoc, mvDualMap_comp, mvDualMap_comp]
    exact congrArg (fun φ => dualMap2 φ) (corestrict_comp_subToAllV U V hUV)
  refine eltSub_ext _ p ?_
  rw [hom_eltSub]
  have h := congrArg (fun φ => ((φ.f p).hom c)) hcx
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  exact (congrArg ((subCxDualIso ((V : Opens X) : Set X)).hom.f p).hom hA).trans h

end MVDelta

end

end GroupApproximation.CharClass
