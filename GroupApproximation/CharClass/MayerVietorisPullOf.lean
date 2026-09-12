import GroupApproximation.CharClass.MayerVietorisElementOf
import GroupApproximation.CharClass.MayerVietorisNaturality

/-!
# The Mayer–Vietoris restrictions over a field are the honest pullbacks

The coefficient-generic form of `MayerVietorisPull`, `MayerVietorisPullAmbient` and the four
restriction squares of `MayerVietorisNaturality`.  Every one of the four restrictions of
`MayerVietorisElementOf` is `cohPullbackK K` along the inclusion of subspaces, and so each
commutes with a map of covered spaces by functoriality of `pull`.

The mathematical content is the chain-level naturality square of `subChainCorestrict`
(`subChainCorestrict_naturalityOf`) and the defining property of `subChainCorestrict`
against the small-chain inclusion (`subChainCorestrict_comp_toAllOf`); everything else is
dualization and bookkeeping, exactly as over `F₂`.

## Where the sign goes

`g` of the dual sequence is the dual of `biprod.lift ι (−ι')`, so `mvCxInclVOf ≫ g` is
**minus** the dual of the subordinate-chain inclusion (`mvCxInclVOf_comp_g`), and the
composite through the middle term is minus the pullback.  `mvResWVOf` is defined as the
negative of that composite, so `mvResWVOf_eq_pull` holds with no sign: the two minuses
cancel.  Over `F₂` the first minus was absorbed by `neg_eq_self_chainHom` instead.

## Main results

* `mvResUOf_eq_pull`, `mvResVOf_eq_pull`, `mvResWUOf_eq_pull`, `mvResWVOf_eq_pull`.
* `mvResUOf_naturality`, `mvResVOf_naturality`, `mvResWUOf_naturality`,
  `mvResWVOf_naturality`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X Y : TopCat.{0}}

/-! ## 1. Chain-level bookkeeping over `K` -/

/-- The singular chain complex functor with coefficients in `K`. -/
abbrev chainCxFunOf (K : Type) [CommRing K] : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} K) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} K)).obj (ModuleCat.of K K)

/-- The dualization turns a negated chain map into the negated dual. -/
theorem mvDualMapOf_neg {K : Type} [CommRing K] {C D : ChainComplex (ModuleCat.{0} K) ℕ}
    (f : C ⟶ D) : dualMapOf K (-f) = -dualMapOf K f := by
  show (dualCxFunctorOf K).map (-f).op = -(dualCxFunctorOf K).map f.op
  rw [CategoryTheory.op_neg, CategoryTheory.Functor.map_neg]

/-- **`subChainCorestrict` is natural for inclusions of subspaces**, over any coefficient
ring. -/
theorem subChainCorestrict_naturalityOf (K : Type) [CommRing K] {S T : Set X} (h : S ⊆ T) :
    subChainCorestrict K X S ≫ subChainInclusion (R := K) S T h
      = (chainCxFunOf K).map (subInclusion h) ≫ subChainCorestrict K X T := by
  have hc : (chainCxFunOf K).map (subInclusion h) ≫ (chainCxFunOf K).map (sInclusion T)
      = (chainCxFunOf K).map (sInclusion S) := by
    rw [← CategoryTheory.Functor.map_comp, subInclusion_comp_sInclusion]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  have hn : ((chainCxFunOf K).map (subInclusion h)).f n
      ≫ ((chainCxFunOf K).map (sInclusion T)).f n
      = ((chainCxFunOf K).map (sInclusion S)).f n := by
    rw [← HomologicalComplex.comp_f, hc]
  exact (hom_apply_of_comp_eq hn c).symm

/-- The dual of the naturality square of `subChainCorestrict`. -/
theorem dualMapOf_subChainCorestrict_naturality (K : Type) [CommRing K] {S T : Set X}
    (h : S ⊆ T) :
    dualMapOf K (subChainInclusion (R := K) S T h) ≫ dualMapOf K (subChainCorestrict K X S)
      = dualMapOf K (subChainCorestrict K X T)
          ≫ dualMapOf K ((chainCxFunOf K).map (subInclusion h)) := by
  rw [mvDualMapOf_comp, mvDualMapOf_comp, subChainCorestrict_naturalityOf K h]

/-- The `U`-inclusion of the dual biproduct, followed by `g`, is the dual of the inclusion of
subordinate chains. -/
theorem mvCxInclUOf_comp_g (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvCxInclUOf K U V ≫ (mvCoSCOf K U V hUV).g
      = dualMapOf K (subChainInclusion (R := K) ((U : Set X) ∩ (V : Set X)) (U : Set X)
          Set.inter_subset_left) := by
  have hlift : mvLeftChainMap K U V hUV ≫ biprod.fst
      = subChainInclusion (R := K) ((U : Set X) ∩ (V : Set X)) (U : Set X)
          Set.inter_subset_left := by
    show biprod.lift (mvInclUV_U K U V) (-(mvInclUV_V K U V)) ≫ biprod.fst = _
    rw [biprod.lift_fst]
    rfl
  show dualMapOf K (biprod.fst (X := mvCxOf K U) (Y := mvCxOf K V))
      ≫ dualMapOf K (mvLeftChainMap K U V hUV) = _
  rw [mvDualMapOf_comp, hlift]

/-- The `V` twin: here the minus of `mvLeftChainMap` survives. -/
theorem mvCxInclVOf_comp_g (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    mvCxInclVOf K U V ≫ (mvCoSCOf K U V hUV).g
      = -dualMapOf K (subChainInclusion (R := K) ((U : Set X) ∩ (V : Set X)) (V : Set X)
          Set.inter_subset_right) := by
  have hlift : mvLeftChainMap K U V hUV ≫ biprod.snd
      = -subChainInclusion (R := K) ((U : Set X) ∩ (V : Set X)) (V : Set X)
          Set.inter_subset_right := by
    show biprod.lift (mvInclUV_U K U V) (-(mvInclUV_V K U V)) ≫ biprod.snd = _
    rw [biprod.lift_snd]
    rfl
  show dualMapOf K (biprod.snd (X := mvCxOf K U) (Y := mvCxOf K V))
      ≫ dualMapOf K (mvLeftChainMap K U V hUV) = _
  rw [mvDualMapOf_comp, hlift, mvDualMapOf_neg]

/-! ## 2. The restrictions to the intersection -/

/-- **The restriction of the first piece to the intersection is the honest pullback.** -/
theorem mvResWUOf_eq_pull (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    mvResWUOf K U V hUV n
      = cohPullbackK K (subInclusion (Set.inter_subset_left (s := (U : Set X))
          (t := (V : Set X)))) n := by
  have key : mvHInclUOf K U V n ≫ mvPsiOf K U V hUV n
      = (subCxDualHomologyIsoOf K (U : Set X) n).hom
          ≫ cohPullbackK K (subInclusion (Set.inter_subset_left (s := (U : Set X))
              (t := (V : Set X)))) n := by
    have h2 : mvHInclUOf K U V n ≫ HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n
        = HomologicalComplex.homologyMap
            (dualMapOf K (subChainInclusion (R := K) ((U : Set X) ∩ (V : Set X)) (U : Set X)
              Set.inter_subset_left)) n := by
      have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
        (mvCxInclUOf_comp_g K U V hUV)
      simp only [HomologicalComplex.homologyMap_comp] at hc
      exact hc
    show mvHInclUOf K U V n ≫ HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n
        ≫ HomologicalComplex.homologyMap
            (dualMapOf K (subChainCorestrict K X ((U : Set X) ∩ (V : Set X)))) n
      = HomologicalComplex.homologyMap
            (dualMapOf K (subChainCorestrict K X (U : Set X))) n
        ≫ HomologicalComplex.homologyMap
            (dualMapOf K ((chainCxFunOf K).map (subInclusion (Set.inter_subset_left
              (s := (U : Set X)) (t := (V : Set X)))))) n
    rw [← Category.assoc, h2]
    have hnat := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (dualMapOf_subChainCorestrict_naturality K
        (Set.inter_subset_left (s := (U : Set X)) (t := (V : Set X))))
    simp only [HomologicalComplex.homologyMap_comp] at hnat
    exact hnat
  show (subCxDualHomologyIsoOf K (U : Set X) n).inv ≫ mvHInclUOf K U V n
      ≫ mvPsiOf K U V hUV n = _
  rw [key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The restriction of the second piece to the intersection is the honest pullback.**  The
minus of `mvCxInclVOf_comp_g` cancels the one in the definition of `mvResWVOf`. -/
theorem mvResWVOf_eq_pull (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    mvResWVOf K U V hUV n
      = cohPullbackK K (subInclusion (Set.inter_subset_right (s := (U : Set X))
          (t := (V : Set X)))) n := by
  have key : mvHInclVOf K U V n ≫ mvPsiOf K U V hUV n
      = -((subCxDualHomologyIsoOf K (V : Set X) n).hom
          ≫ cohPullbackK K (subInclusion (Set.inter_subset_right (s := (U : Set X))
              (t := (V : Set X)))) n) := by
    have h2 : mvHInclVOf K U V n ≫ HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n
        = -HomologicalComplex.homologyMap
            (dualMapOf K (subChainInclusion (R := K) ((U : Set X) ∩ (V : Set X)) (V : Set X)
              Set.inter_subset_right)) n := by
      have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
        (mvCxInclVOf_comp_g K U V hUV)
      simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg] at hc
      exact hc
    show mvHInclVOf K U V n ≫ HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n
        ≫ HomologicalComplex.homologyMap
            (dualMapOf K (subChainCorestrict K X ((U : Set X) ∩ (V : Set X)))) n
      = -(HomologicalComplex.homologyMap
            (dualMapOf K (subChainCorestrict K X (V : Set X))) n
        ≫ HomologicalComplex.homologyMap
            (dualMapOf K ((chainCxFunOf K).map (subInclusion (Set.inter_subset_right
              (s := (U : Set X)) (t := (V : Set X)))))) n)
    rw [← Category.assoc, h2, Preadditive.neg_comp]
    have hnat := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (dualMapOf_subChainCorestrict_naturality K
        (Set.inter_subset_right (s := (U : Set X)) (t := (V : Set X))))
    simp only [HomologicalComplex.homologyMap_comp] at hnat
    rw [hnat]
  show -((subCxDualHomologyIsoOf K (V : Set X) n).inv ≫ mvHInclVOf K U V n
      ≫ mvPsiOf K U V hUV n) = _
  rw [key, Preadditive.comp_neg, neg_neg, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-! ## 3. The restrictions from the ambient space -/

/-- Corestricting to the subordinate chains and including into all chains is the chain map
of the inclusion of the subspace, over any coefficient ring. -/
theorem subChainCorestrict_comp_toAllOf (K : Type) [CommRing K] (U V : Opens X)
    (hUV : U ⊔ V = ⊤) :
    subChainCorestrict K X (U : Set X)
        ≫ (mvInclU_small K U V hUV ≫ smallChainsInclusion K X (twoSetCover U V hUV))
      = (chainCxFunOf K).map (sInclusion (U : Set X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- The `V` twin of `subChainCorestrict_comp_toAllOf`. -/
theorem subChainCorestrict_comp_toAllVOf (K : Type) [CommRing K] (U V : Opens X)
    (hUV : U ⊔ V = ⊤) :
    subChainCorestrict K X (V : Set X)
        ≫ (mvInclV_small K U V hUV ≫ smallChainsInclusion K X (twoSetCover U V hUV))
      = (chainCxFunOf K).map (sInclusion (V : Set X)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

theorem f_comp_mvCxProjUOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSCOf K U V hUV).f ≫ mvCxProjUOf K U V = dualMapOf K (mvInclU_small K U V hUV) := by
  show dualMapOf K (mvRightChainMap K U V hUV)
      ≫ dualMapOf K (biprod.inl (X := mvCxOf K U) (Y := mvCxOf K V)) = _
  rw [mvDualMapOf_comp]
  congr 1
  exact biprod.inl_desc _ _

theorem f_comp_mvCxProjVOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSCOf K U V hUV).f ≫ mvCxProjVOf K U V = dualMapOf K (mvInclV_small K U V hUV) := by
  show dualMapOf K (mvRightChainMap K U V hUV)
      ≫ dualMapOf K (biprod.inr (X := mvCxOf K U) (Y := mvCxOf K V)) = _
  rw [mvDualMapOf_comp]
  congr 1
  exact biprod.inr_desc _ _

/-- **The restriction from the ambient space to the first piece is the honest pullback.** -/
theorem mvResUOf_eq_pull (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    mvResUOf K U V hUV n = cohPullbackK K (sInclusion (U : Set X)) n := by
  have hA : HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n ≫ mvHProjUOf K U V n
      = HomologicalComplex.homologyMap (dualMapOf K (mvInclU_small K U V hUV)) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (f_comp_mvCxProjUOf K U V hUV)
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  have hB : dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))
        ≫ dualMapOf K (mvInclU_small K U V hUV)
        ≫ dualMapOf K (subChainCorestrict K X (U : Set X))
      = dualMapOf K ((chainCxFunOf K).map (sInclusion (U : Set X))) := by
    rw [← Category.assoc, mvDualMapOf_comp, mvDualMapOf_comp]
    exact congrArg (fun φ => dualMapOf K φ) (subChainCorestrict_comp_toAllOf K U V hUV)
  have hBh : HomologicalComplex.homologyMap
        (dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))) n
      ≫ (HomologicalComplex.homologyMap (dualMapOf K (mvInclU_small K U V hUV)) n
          ≫ HomologicalComplex.homologyMap
              (dualMapOf K (subChainCorestrict K X (U : Set X))) n)
      = HomologicalComplex.homologyMap
          (dualMapOf K ((chainCxFunOf K).map (sInclusion (U : Set X)))) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hB
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hBx : (subCxDualHomologyIsoOf K (U : Set X) n).hom.hom
        ((HomologicalComplex.homologyMap (dualMapOf K (mvInclU_small K U V hUV)) n).hom
          ((mvAmbientIsoOf K U V hUV n).inv.hom x))
      = (HomologicalComplex.homologyMap
          (dualMapOf K ((chainCxFunOf K).map (sInclusion (U : Set X)))) n).hom x := by
    have h := hom_apply_of_comp_eq hBh x
    rw [hom_apply_comp] at h
    exact h
  show (subCxDualHomologyIsoOf K (U : Set X) n).hom.hom ((mvHProjUOf K U V n).hom
      ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n).hom
        ((mvAmbientIsoOf K U V hUV n).inv.hom x)))
    = (HomologicalComplex.homologyMap
        (dualMapOf K ((chainCxFunOf K).map (sInclusion (U : Set X)))) n).hom x
  rw [← hBx]
  congr 1
  exact hom_apply_of_comp_eq hA _

/-- **The restriction from the ambient space to the second piece is the honest pullback.** -/
theorem mvResVOf_eq_pull (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    mvResVOf K U V hUV n = cohPullbackK K (sInclusion (V : Set X)) n := by
  have hA : HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n ≫ mvHProjVOf K U V n
      = HomologicalComplex.homologyMap (dualMapOf K (mvInclV_small K U V hUV)) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (f_comp_mvCxProjVOf K U V hUV)
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  have hB : dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))
        ≫ dualMapOf K (mvInclV_small K U V hUV)
        ≫ dualMapOf K (subChainCorestrict K X (V : Set X))
      = dualMapOf K ((chainCxFunOf K).map (sInclusion (V : Set X))) := by
    rw [← Category.assoc, mvDualMapOf_comp, mvDualMapOf_comp]
    exact congrArg (fun φ => dualMapOf K φ) (subChainCorestrict_comp_toAllVOf K U V hUV)
  have hBh : HomologicalComplex.homologyMap
        (dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))) n
      ≫ (HomologicalComplex.homologyMap (dualMapOf K (mvInclV_small K U V hUV)) n
          ≫ HomologicalComplex.homologyMap
              (dualMapOf K (subChainCorestrict K X (V : Set X))) n)
      = HomologicalComplex.homologyMap
          (dualMapOf K ((chainCxFunOf K).map (sInclusion (V : Set X)))) n := by
    have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hB
    simp only [HomologicalComplex.homologyMap_comp] at hc
    exact hc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hBx : (subCxDualHomologyIsoOf K (V : Set X) n).hom.hom
        ((HomologicalComplex.homologyMap (dualMapOf K (mvInclV_small K U V hUV)) n).hom
          ((mvAmbientIsoOf K U V hUV n).inv.hom x))
      = (HomologicalComplex.homologyMap
          (dualMapOf K ((chainCxFunOf K).map (sInclusion (V : Set X)))) n).hom x := by
    have h := hom_apply_of_comp_eq hBh x
    rw [hom_apply_comp] at h
    exact h
  show (subCxDualHomologyIsoOf K (V : Set X) n).hom.hom ((mvHProjVOf K U V n).hom
      ((HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n).hom
        ((mvAmbientIsoOf K U V hUV n).inv.hom x)))
    = (HomologicalComplex.homologyMap
        (dualMapOf K ((chainCxFunOf K).map (sInclusion (V : Set X)))) n).hom x
  rw [← hBx]
  congr 1
  exact hom_apply_of_comp_eq hA _

/-! ## 4. Naturality in a map of covered spaces -/

/-- **Naturality of the restriction to the first piece**, over a field. -/
theorem mvResUOf_naturality (K : Type) [Field K] (f : Y ⟶ X) (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (x : Hmod K X n) :
    (mvResUOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull f n x)
      = pull (opensRestrict f U) n ((mvResUOf K U V hUV n).hom x) := by
  rw [mvResUOf_eq_pull, mvResUOf_eq_pull]
  show pull (sInclusion ((opensComap f U : Opens Y) : Set Y)) n (pull f n x)
      = pull (opensRestrict f U) n (pull (sInclusion ((U : Opens X) : Set X)) n x)
  rw [← pull_comp, ← pull_comp, opensRestrict_comp_sInclusion]

/-- **Naturality of the restriction to the second piece**, over a field. -/
theorem mvResVOf_naturality (K : Type) [Field K] (f : Y ⟶ X) (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (x : Hmod K X n) :
    (mvResVOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull f n x)
      = pull (opensRestrict f V) n ((mvResVOf K U V hUV n).hom x) := by
  rw [mvResVOf_eq_pull, mvResVOf_eq_pull]
  show pull (sInclusion ((opensComap f V : Opens Y) : Set Y)) n (pull f n x)
      = pull (opensRestrict f V) n (pull (sInclusion ((V : Opens X) : Set X)) n x)
  rw [← pull_comp, ← pull_comp, opensRestrict_comp_sInclusion]

/-- **Naturality of the restriction of the first piece to the intersection.** -/
theorem mvResWUOf_naturality (K : Type) [CommRing K] (f : Y ⟶ X) (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (a : Hmod K (mvU U) n) :
    (mvResWUOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull (opensRestrict f U) n a)
      = pull (interRestrict f U V) n ((mvResWUOf K U V hUV n).hom a) := by
  rw [mvResWUOf_eq_pull, mvResWUOf_eq_pull]
  show pull (subInclusion (Set.inter_subset_left
        (s := ((opensComap f U : Opens Y) : Set Y))
        (t := ((opensComap f V : Opens Y) : Set Y)))) n (pull (opensRestrict f U) n a)
      = pull (interRestrict f U V) n
          (pull (subInclusion (Set.inter_subset_left
            (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))) n a)
  rw [← pull_comp, ← pull_comp, interRestrict_comp_subInclusionLeft]

/-- **Naturality of the restriction of the second piece to the intersection.** -/
theorem mvResWVOf_naturality (K : Type) [CommRing K] (f : Y ⟶ X) (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (b : Hmod K (mvU V) n) :
    (mvResWVOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull (opensRestrict f V) n b)
      = pull (interRestrict f U V) n ((mvResWVOf K U V hUV n).hom b) := by
  rw [mvResWVOf_eq_pull, mvResWVOf_eq_pull]
  show pull (subInclusion (Set.inter_subset_right
        (s := ((opensComap f U : Opens Y) : Set Y))
        (t := ((opensComap f V : Opens Y) : Set Y)))) n (pull (opensRestrict f V) n b)
      = pull (interRestrict f U V) n
          (pull (subInclusion (Set.inter_subset_right
            (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))) n b)
  rw [← pull_comp, ← pull_comp, interRestrict_comp_subInclusionRight]

end

end GroupApproximation.CharClass
