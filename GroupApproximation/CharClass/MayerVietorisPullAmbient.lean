import GroupApproximation.CharClass.MayerVietorisPull

/-!
# The Mayer–Vietoris restriction from the ambient space is the honest pullback

`MayerVietorisPull.lean` identifies the restriction `H^n(U) → H^n(U ∩ V)` with the
pullback along the inclusion of subspaces.  This file does the same for the restriction
`H^n(X) → H^n(U)` from the ambient space, which is the harder of the two because it
goes through the *small-chain* end of the dualized sequence, where `mvAmbientIso`
inverts a quasi-isomorphism.

The point is that the inverse is not needed.  `mvAmbientIso.inv` is definitionally
`homologyMap (dualMap2 (smallChainsInclusion …)) n`, so the whole composite is a single
`homologyMap` of a composite of duals, and the chain-level identity behind it is

```text
subChainCorestrict S ≫ (subordinate chains ↪ small chains ↪ all chains)
  = chainCxFun.map (sInclusion S),
```

which is `subChainCorestrict`'s defining property: it is the corestriction of exactly
that map.  Both sides send a chain of `↥S` to its image in the chains of `X`.

With this and `mvResWU_eq_pull`, every Mayer–Vietoris restriction is a `cohPullback`,
so the restriction squares of naturality in a map of covered spaces are functoriality
of `pull` and need no new chain-level machinery; only the δ-square does.

## Main results

* `subChainCorestrict_comp_toAll` — the chain-level identity.
* `mvResU_eq_pull` — `mvResU` is `cohPullback` along `sInclusion`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **Corestricting to the subordinate chains and then including into all chains is the
chain map induced by the inclusion of the subspace.** -/
theorem subChainCorestrict_comp_toAll (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainCorestrict (ZMod 2) X (U : Set X)
        ≫ (mvInclU_small (ZMod 2) U V hUV
            ≫ smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))
      = chainCxFun.map (sInclusion (U : Set X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- The first map of the dual sequence, followed by the `U`-component, is the dual of the
inclusion of the subordinate chains into the small chains. -/
theorem f_comp_mvCxProjU (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSC U V hUV).f ≫ mvCxProjU U V = dualMap2 (mvInclU_small (ZMod 2) U V hUV) := by
  show dualMap2 (mvRightChainMap (ZMod 2) U V hUV)
      ≫ dualMap2 (biprod.inl (X := mvCx U) (Y := mvCx V)) = _
  rw [mvDualMap_comp]
  congr 1
  exact biprod.inl_desc _ _

/-- **The Mayer–Vietoris restriction from the ambient space is the honest pullback.** -/
theorem mvResU_eq_pull (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    mvResU U V hUV n = cohPullback (sInclusion (U : Set X)) n := by
  have hA : HomologicalComplex.homologyMap (mvCoSC U V hUV).f n ≫ mvHProjU U V n
      = HomologicalComplex.homologyMap (dualMap2 (mvInclU_small (ZMod 2) U V hUV)) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (f_comp_mvCxProjU U V hUV)
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  have hB : dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))
        ≫ dualMap2 (mvInclU_small (ZMod 2) U V hUV)
        ≫ dualMap2 (subChainCorestrict (ZMod 2) X (U : Set X))
      = dualMap2 (chainCxFun.map (sInclusion (U : Set X))) := by
    rw [← Category.assoc, mvDualMap_comp, mvDualMap_comp]
    exact congrArg (fun φ => dualMap2 φ) (subChainCorestrict_comp_toAll U V hUV)
  have hBh : HomologicalComplex.homologyMap
        (dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n
      ≫ (HomologicalComplex.homologyMap (dualMap2 (mvInclU_small (ZMod 2) U V hUV)) n
          ≫ HomologicalComplex.homologyMap
              (dualMap2 (subChainCorestrict (ZMod 2) X (U : Set X))) n)
      = HomologicalComplex.homologyMap
          (dualMap2 (chainCxFun.map (sInclusion (U : Set X)))) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hB
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hBx : (subCxDualHomologyIso (U : Set X) n).hom.hom
        ((HomologicalComplex.homologyMap (dualMap2 (mvInclU_small (ZMod 2) U V hUV)) n).hom
          ((mvAmbientIso U V hUV n).inv.hom x))
      = (HomologicalComplex.homologyMap
          (dualMap2 (chainCxFun.map (sInclusion (U : Set X)))) n).hom x := by
    have h := hom_apply_of_comp_eq hBh x
    rw [hom_apply_comp] at h
    exact h
  show (subCxDualHomologyIso (U : Set X) n).hom.hom ((mvHProjU U V n).hom
      ((HomologicalComplex.homologyMap (mvCoSC U V hUV).f n).hom
        ((mvAmbientIso U V hUV n).inv.hom x)))
    = (HomologicalComplex.homologyMap
        (dualMap2 (chainCxFun.map (sInclusion (U : Set X)))) n).hom x
  rw [← hBx]
  congr 1
  exact hom_apply_of_comp_eq hA _

/-! ## The `V` twin

Identical, with `biprod.inr_desc` in place of `biprod.inl_desc`.  There is no sign to
absorb: the minus of the chain-level Mayer–Vietoris lives in `mvLeftChainMap`, which is
`g`, and this is the `f` side. -/

/-- The `V` twin of `subChainCorestrict_comp_toAll`. -/
theorem subChainCorestrict_comp_toAllV (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainCorestrict (ZMod 2) X (V : Set X)
        ≫ (mvInclV_small (ZMod 2) U V hUV
            ≫ smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))
      = chainCxFun.map (sInclusion (V : Set X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- The `V` twin of `f_comp_mvCxProjU`. -/
theorem f_comp_mvCxProjV (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSC U V hUV).f ≫ mvCxProjV U V = dualMap2 (mvInclV_small (ZMod 2) U V hUV) := by
  show dualMap2 (mvRightChainMap (ZMod 2) U V hUV)
      ≫ dualMap2 (biprod.inr (X := mvCx U) (Y := mvCx V)) = _
  rw [mvDualMap_comp]
  congr 1
  exact biprod.inr_desc _ _

/-- **The Mayer–Vietoris restriction to the second piece is the honest pullback.**
`cc-projective` uses this for stability of the degree-two generator along the hyperplane
inclusion, hence for invariance of the Euler class under isomorphism of line bundles. -/
theorem mvResV_eq_pull (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    mvResV U V hUV n = cohPullback (sInclusion (V : Set X)) n := by
  have hA : HomologicalComplex.homologyMap (mvCoSC U V hUV).f n ≫ mvHProjV U V n
      = HomologicalComplex.homologyMap (dualMap2 (mvInclV_small (ZMod 2) U V hUV)) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (f_comp_mvCxProjV U V hUV)
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  have hB : dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))
        ≫ dualMap2 (mvInclV_small (ZMod 2) U V hUV)
        ≫ dualMap2 (subChainCorestrict (ZMod 2) X (V : Set X))
      = dualMap2 (chainCxFun.map (sInclusion (V : Set X))) := by
    rw [← Category.assoc, mvDualMap_comp, mvDualMap_comp]
    exact congrArg (fun φ => dualMap2 φ) (subChainCorestrict_comp_toAllV U V hUV)
  have hBh : HomologicalComplex.homologyMap
        (dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n
      ≫ (HomologicalComplex.homologyMap (dualMap2 (mvInclV_small (ZMod 2) U V hUV)) n
          ≫ HomologicalComplex.homologyMap
              (dualMap2 (subChainCorestrict (ZMod 2) X (V : Set X))) n)
      = HomologicalComplex.homologyMap
          (dualMap2 (chainCxFun.map (sInclusion (V : Set X)))) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hB
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hBx : (subCxDualHomologyIso (V : Set X) n).hom.hom
        ((HomologicalComplex.homologyMap (dualMap2 (mvInclV_small (ZMod 2) U V hUV)) n).hom
          ((mvAmbientIso U V hUV n).inv.hom x))
      = (HomologicalComplex.homologyMap
          (dualMap2 (chainCxFun.map (sInclusion (V : Set X)))) n).hom x := by
    have h := hom_apply_of_comp_eq hBh x
    rw [hom_apply_comp] at h
    exact h
  show (subCxDualHomologyIso (V : Set X) n).hom.hom ((mvHProjV U V n).hom
      ((HomologicalComplex.homologyMap (mvCoSC U V hUV).f n).hom
        ((mvAmbientIso U V hUV n).inv.hom x)))
    = (HomologicalComplex.homologyMap
        (dualMap2 (chainCxFun.map (sInclusion (V : Set X)))) n).hom x
  rw [← hBx]
  congr 1
  exact hom_apply_of_comp_eq hA _

end

end GroupApproximation.CharClass
