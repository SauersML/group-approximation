import GroupApproximation.CharClass.MayerVietorisRestriction

/-!
# The Mayer–Vietoris restrictions are the honest pullbacks

`MayerVietorisElement.lean` builds `mvResWU` out of the dualized Mayer–Vietoris
sequence, so it unfolds to a homology map conjugated by two identification
isomorphisms.  This file identifies it with `cohPullback` along the inclusion of the
intersection into the piece, and records the degree-zero corollary that the unit class
restricts to the unit — which is the last hypothesis of `cc-projective`'s
projective-space induction.

The mathematical content is `MayerVietorisRestriction.subChainCorestrict_naturality`;
everything here is dualization and bookkeeping:

* `mvCxInclU ≫ (mvCoSC …).g = dualMap2 (subChainInclusion …)`, by contravariant
  functoriality of `dualMap2` and `biprod.lift_fst`;
* `(subCxDualHomologyIso S n).hom` is `homologyMap (dualMap2 (subChainCorestrict … S)) n`
  and `cohPullback f n` is `homologyMap (dualMap2 (chainCxFun.map f)) n`, both
  definitionally;
* so the naturality square, dualized and pushed through `homologyMap`, is exactly the
  required identity.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- The `U`-inclusion of the dual biproduct, followed by the second map of the dual
Mayer–Vietoris sequence, is the dual of the inclusion of subordinate chains. -/
theorem mvCxInclU_comp_g (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvCxInclU U V ≫ (mvCoSC U V hUV).g
      = dualMap2 (subChainInclusion ((U : Set X) ∩ (V : Set X)) (U : Set X)
          Set.inter_subset_left) := by
  have hlift : mvLeftChainMap (ZMod 2) U V hUV ≫ biprod.fst
      = subChainInclusion ((U : Set X) ∩ (V : Set X)) (U : Set X) Set.inter_subset_left := by
    show biprod.lift (mvInclUV_U (ZMod 2) U V) (-(mvInclUV_V (ZMod 2) U V)) ≫ biprod.fst = _
    rw [biprod.lift_fst]
    rfl
  show dualMap2 (biprod.fst (X := mvCx U) (Y := mvCx V))
      ≫ dualMap2 (mvLeftChainMap (ZMod 2) U V hUV) = _
  rw [mvDualMap_comp, hlift]

/-- The dual of the naturality square of `subChainCorestrict`. -/
theorem dualMap2_subChainCorestrict_naturality {S T : Set X} (h : S ⊆ T) :
    dualMap2 (subChainInclusion S T h) ≫ dualMap2 (subChainCorestrict (ZMod 2) X S)
      = dualMap2 (subChainCorestrict (ZMod 2) X T)
          ≫ dualMap2 (chainCxFun.map (subInclusion h)) := by
  rw [mvDualMap_comp, mvDualMap_comp, subChainCorestrict_naturality h]

/-- **The Mayer–Vietoris restriction to the intersection is the honest pullback** along
the inclusion of the intersection into the piece. -/
theorem mvResWU_eq_pull (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    mvResWU U V hUV n
      = cohPullback (subInclusion (Set.inter_subset_left (s := (U : Set X))
          (t := (V : Set X)))) n := by
  have key : mvHInclU U V n ≫ mvPsi U V hUV n
      = (subCxDualHomologyIso (U : Set X) n).hom
          ≫ cohPullback (subInclusion (Set.inter_subset_left (s := (U : Set X))
              (t := (V : Set X)))) n := by
    have h2 : mvHInclU U V n ≫ HomologicalComplex.homologyMap (mvCoSC U V hUV).g n
        = HomologicalComplex.homologyMap
            (dualMap2 (subChainInclusion ((U : Set X) ∩ (V : Set X)) (U : Set X)
              Set.inter_subset_left)) n := by
      have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
        (mvCxInclU_comp_g U V hUV)
      simp only [HomologicalComplex.homologyMap_comp] at hc
      exact hc
    show mvHInclU U V n ≫ HomologicalComplex.homologyMap (mvCoSC U V hUV).g n
        ≫ HomologicalComplex.homologyMap
            (dualMap2 (subChainCorestrict (ZMod 2) X ((U : Set X) ∩ (V : Set X)))) n
      = HomologicalComplex.homologyMap
            (dualMap2 (subChainCorestrict (ZMod 2) X (U : Set X))) n
        ≫ HomologicalComplex.homologyMap
            (dualMap2 (chainCxFun.map (subInclusion (Set.inter_subset_left
              (s := (U : Set X)) (t := (V : Set X)))))) n
    rw [← Category.assoc, h2]
    have hnat := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (dualMap2_subChainCorestrict_naturality
        (Set.inter_subset_left (s := (U : Set X)) (t := (V : Set X))))
    simp only [HomologicalComplex.homologyMap_comp] at hnat
    exact hnat
  show (subCxDualHomologyIso (U : Set X) n).inv ≫ mvHInclU U V n ≫ mvPsi U V hUV n = _
  rw [key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The unit restricts to the unit.**  This is the degree-zero corollary that makes
`cc-projective`'s `H^*(ℂP^n; F₂)` unconditional. -/
theorem mvResWU_one (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvResWU U V hUV 0).hom (one (mvU U)) = one (mvInter U V) := by
  rw [mvResWU_eq_pull]
  exact pull_one _

end

end GroupApproximation.CharClass
