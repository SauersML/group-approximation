import GroupApproximation.CharClass.CohomologyClassOf
import GroupApproximation.CharClass.MayerVietorisPull

/-!
# The two maps of the Mayer–Vietoris sequence, identified on the chain level

To compute the connecting map on cochains one has to know what the two maps of
`mvCoSC` do.  `cc-thom`'s `MayerVietorisPull.lean` identifies the `U`-component of
`g` with the dual of an inclusion of subordinate chains; this file adds the three
pieces that were not there:

* the `V` twin, where the sign in `mvLeftChainMap` disappears because `-φ = φ` for a
  morphism of `F₂` complexes;
* the two components of `f`, which are the duals of the inclusions of the
  subordinate chains of a piece into the small chains;
* `subToAll`, the inclusion of the subordinate chains of a piece into **all**
  singular chains, and the identity saying that precomposing it with
  `subChainCorestrict` is the singular chain map of the subspace inclusion.

Together they say: under the identifications, `g` is the difference of the two
restrictions and `f` is the pair of restrictions from the ambient space.

## Main declarations

* `MVDelta.neg_eq_self_hom`, `MVDelta.mvDualMap_neg`.
* `MVDelta.mvCxInclV_comp_g`.
* `MVDelta.f_comp_projU`, `MVDelta.f_comp_projV`.
* `MVDelta.subToAllU`, `MVDelta.subToAllV`, and the two `corestrict_comp_subToAll`
  identities.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X : TopCat.{0}}

/-! ## 1. Signs disappear mod 2 -/

/-- A morphism of `F₂` cochain complexes is its own negative. -/
theorem neg_eq_self_hom {K L : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (φ : K ⟶ L) :
    -φ = φ := by
  refine neg_eq_of_add_eq_zero_right ?_
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show (φ.f n).hom x + (φ.f n).hom x = 0
  exact add_self_eq_zero_two _

/-- The dualization does not see a sign. -/
theorem mvDualMap_neg {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L) :
    dualMap2 (-f) = dualMap2 f := by
  show dualCxFunctor.map (-f).op = dualCxFunctor.map f.op
  rw [op_neg, Functor.map_neg, neg_eq_self_hom]

/-! ## 2. The second map of the sequence is the pair of restrictions -/

/-- The `V` twin of `cc-thom`'s `mvCxInclU_comp_g`. -/
theorem mvCxInclV_comp_g (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvCxInclV U V ≫ (mvCoSC U V hUV).g
      = dualMap2 (subChainInclusion ((U : Set X) ∩ (V : Set X)) (V : Set X)
          Set.inter_subset_right) := by
  have hlift : mvLeftChainMap (ZMod 2) U V hUV ≫ biprod.snd
      = -(subChainInclusion ((U : Set X) ∩ (V : Set X)) (V : Set X)
          Set.inter_subset_right) := by
    show biprod.lift (mvInclUV_U (ZMod 2) U V) (-(mvInclUV_V (ZMod 2) U V)) ≫ biprod.snd = _
    rw [biprod.lift_snd]
    rfl
  show dualMap2 (biprod.snd (X := mvCx U) (Y := mvCx V))
      ≫ dualMap2 (mvLeftChainMap (ZMod 2) U V hUV) = _
  rw [mvDualMap_comp, hlift, mvDualMap_neg]

/-! ## 3. The first map of the sequence is the pair of restrictions from the ambient -/

theorem f_comp_projU (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSC U V hUV).f ≫ mvCxProjU U V = dualMap2 (mvInclU_small (ZMod 2) U V hUV) := by
  have hd : biprod.inl (X := mvCx U) (Y := mvCx V) ≫ mvRightChainMap (ZMod 2) U V hUV
      = mvInclU_small (ZMod 2) U V hUV := by
    show biprod.inl ≫ biprod.desc (mvInclU_small (ZMod 2) U V hUV)
      (mvInclV_small (ZMod 2) U V hUV) = _
    rw [biprod.inl_desc]
  show dualMap2 (mvRightChainMap (ZMod 2) U V hUV)
      ≫ dualMap2 (biprod.inl (X := mvCx U) (Y := mvCx V)) = _
  rw [mvDualMap_comp, hd]

theorem f_comp_projV (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSC U V hUV).f ≫ mvCxProjV U V = dualMap2 (mvInclV_small (ZMod 2) U V hUV) := by
  have hd : biprod.inr (X := mvCx U) (Y := mvCx V) ≫ mvRightChainMap (ZMod 2) U V hUV
      = mvInclV_small (ZMod 2) U V hUV := by
    show biprod.inr ≫ biprod.desc (mvInclU_small (ZMod 2) U V hUV)
      (mvInclV_small (ZMod 2) U V hUV) = _
    rw [biprod.inr_desc]
  show dualMap2 (mvRightChainMap (ZMod 2) U V hUV)
      ≫ dualMap2 (biprod.inr (X := mvCx U) (Y := mvCx V)) = _
  rw [mvDualMap_comp, hd]

/-! ## 4. Subordinate chains inside all singular chains -/

/-- The subordinate chains of `U` inside all singular chains of `X`. -/
def subToAllU (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvCx U ⟶ singularChainComplex (ZMod 2) X :=
  mvInclU_small (ZMod 2) U V hUV ≫ smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV)

/-- The subordinate chains of `V` inside all singular chains of `X`. -/
def subToAllV (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvCx V ⟶ singularChainComplex (ZMod 2) X :=
  mvInclV_small (ZMod 2) U V hUV ≫ smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV)

/-- Corestricting the singular chains of the subspace `U` and then including into all
singular chains of `X` is the singular chain map of the inclusion. -/
theorem corestrict_comp_subToAllU (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainCorestrict (ZMod 2) X (U : Set X) ≫ subToAllU U V hUV
      = chainCxFun.map (sInclusion (U : Set X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

theorem corestrict_comp_subToAllV (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    subChainCorestrict (ZMod 2) X (V : Set X) ≫ subToAllV U V hUV
      = chainCxFun.map (sInclusion (V : Set X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

end MVDelta

end

end GroupApproximation.CharClass
