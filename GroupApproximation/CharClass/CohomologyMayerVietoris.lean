import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.CharClass.RelativeDual
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris

/-!
# Mayer–Vietoris for mod-2 singular cohomology

The vendored development carries the Mayer–Vietoris **short exact sequence of
chain complexes** for two opens `U ⊔ V = ⊤`,

```text
0 → C_*(U ∩ V) → C_*(U) ⊕ C_*(V) → C_*^{U,V}(X) → 0,
```

together with an explicit **degreewise splitting** (`mvSplitting`).  A degreewise
split short exact sequence stays short exact under any additive functor, so
dualizing with `Hom(-, F₂)` (`cc-relative`'s `dualFunctor`, exact because `F₂` is
an injective module over itself) gives the short exact sequence of **cochain**
complexes

```text
0 → C^*_{U,V}(X) → C^*(U) ⊕ C^*(V) → C^*(U ∩ V) → 0,
```

whose homology long exact sequence is Mayer–Vietoris.  Two identifications turn
the outer terms into honest cohomology of spaces:

* `C^*(S)` for `S ⊆ X` is the dual of the subordinate-chain complex, because
  `subChainCorestrict` is an **isomorphism** of chain complexes;
* `H^*(C^*_{U,V}(X)) ≅ H^*(X)` because the small-chain inclusion is a
  quasi-isomorphism and the dual of a quasi-isomorphism is a quasi-isomorphism.

## Main declarations

* `mvCoSC`, `mvCoSC_shortExact` — the cochain-level short exact sequence.
* `mvInterIso`, `mvAmbientIso` — the two identifications of the outer terms.
* `mvDelta` — the connecting map `H^n(U ∩ V; F₂) ⟶ H^{n+1}(X; F₂)`.
* `mvExact_inter`, `mvExact_sum`, `mvExact_ambient` — exactness at the three spots
  of the raw sequence.
* `isZero_mvCoX2` — the middle term vanishes when both `H^n(U)` and `H^n(V)` do.
* `mvConnectingIso` — `H^n(U ∩ V; F₂) ≅ H^{n+1}(X; F₂)` when `U` and `V` have
  vanishing cohomology in degrees `n` and `n+1`; this is the form used to compute
  spheres and projective spaces.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The dualizing functor on complexes -/

/-- The dualizing functor `K ↦ Hom(K, F₂)` from chain complexes to cochain
complexes; `dualCx` and `dualMap` of `RelativeDual.lean` are its object and
morphism parts. -/
abbrev dualCxFunctor : (ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) ⋙
    ((dualFunctor (ZMod 2)).mapHomologicalComplex _)

theorem dualCxFunctor_obj (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :
    dualCxFunctor.obj (Opposite.op K) = dualCx (ZMod 2) K := rfl

theorem dualCxFunctor_map {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L) :
    dualCxFunctor.map f.op = dualMap (ZMod 2) f := rfl

/-! ## 2. The Mayer–Vietoris short exact sequence of cochain complexes -/

/-- The Mayer–Vietoris short complex of **cochain** complexes: the `Hom(-, F₂)`
dual of the vendored chain-level Mayer–Vietoris short complex. -/
def mvCoSC (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ShortComplex (CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :=
  dualCxFunctor.mapShortComplex.obj (mvShortComplex (ZMod 2) U V hUV).op

/-- The degree-`k` piece of the dual Mayer–Vietoris short complex is split: the
vendored chain-level splitting `mvSplitting` is carried through `op` and the
additive dualizing functor. -/
def mvCoSplitting (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (mvCoSC U V hUV)).Splitting :=
  (((mvSplitting (ZMod 2) U V hUV k).ofIso (mvEvalIso (ZMod 2) U V hUV k).symm).op).map
    (dualFunctor (ZMod 2))

theorem mvCoSC_degreewise_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (mvCoSC U V hUV)).ShortExact :=
  (mvCoSplitting U V hUV k).shortExact

/-- **The Mayer–Vietoris short exact sequence of cochain complexes.** -/
theorem mvCoSC_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSC U V hUV).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun k => mvCoSC_degreewise_shortExact U V hUV k)

/-! ## 3. Identifying the outer terms -/

/-- For a subspace `S ⊆ X` the dual of the subordinate-chain complex **is** the
singular cochain complex of `S`: the corestriction of the inclusion is an
isomorphism of chain complexes. -/
def subCxDualIso (S : Set X) :
    dualCx (ZMod 2) (subChainComplex (ZMod 2) X S) ≅ cochainCxZMod2 (TopCat.of S) :=
  dualCxFunctor.mapIso (asIso (subChainCorestrict (ZMod 2) X S)).op.symm

/-- The `H^n` of the dual subordinate-chain complex is `H^n(S; F₂)`. -/
def subCxDualHomologyIso (S : Set X) (n : ℕ) :
    (dualCx (ZMod 2) (subChainComplex (ZMod 2) X S)).homology n
      ≅ Hmod2 (TopCat.of S) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) n).mapIso
    (subCxDualIso S)

/-- The third term of the dual Mayer–Vietoris sequence computes `H^n(U ∩ V; F₂)`. -/
def mvInterIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSC U V hUV).X₃.homology n
      ≅ Hmod2 (TopCat.of ((U : Set X) ∩ (V : Set X))) n :=
  subCxDualHomologyIso ((U : Set X) ∩ (V : Set X)) n

/-- The dual of the small-chain inclusion is a quasi-isomorphism, so the first term
of the dual Mayer–Vietoris sequence computes `H^n(X; F₂)`. -/
def mvAmbientIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSC U V hUV).X₁.homology n ≅ Hmod2 X n :=
  haveI : IsIso (HomologicalComplex.homologyMap
      (dualMap (ZMod 2) (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n) :=
    (HomologicalComplex.quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  (asIso (HomologicalComplex.homologyMap
    (dualMap (ZMod 2) (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n)).symm

/-! ## 4. The connecting map and exactness -/

/-- **The Mayer–Vietoris connecting map** `δ : H^n(U ∩ V; F₂) ⟶ H^{n+1}(X; F₂)`. -/
def mvDelta (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (TopCat.of ((U : Set X) ∩ (V : Set X))) n ⟶ Hmod2 X (n + 1) :=
  (mvInterIso U V hUV n).inv
    ≫ (mvCoSC_shortExact U V hUV).δ n (n + 1) (by simp)
    ≫ (mvAmbientIso U V hUV (n + 1)).hom

/-- Exactness at `H^n` of the third term: `H^n(X₂) → H^n(U ∩ V) →^δ H^{n+1}(X₁)`. -/
theorem mvExact_inter (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).g n)
      ((mvCoSC_shortExact U V hUV).δ n (n + 1) (by simp))
      ((mvCoSC_shortExact U V hUV).comp_δ n (n + 1) (by simp))).Exact :=
  (mvCoSC_shortExact U V hUV).homology_exact₃ n (n + 1) (by simp)

/-- Exactness at the middle term: `H^n(X₁) → H^n(X₂) → H^n(X₃)`. -/
theorem mvExact_sum (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).f n)
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).g n)
      (by rw [← HomologicalComplex.homologyMap_comp, (mvCoSC U V hUV).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (mvCoSC_shortExact U V hUV).homology_exact₂ n

/-- Exactness at `H^{n+1}` of the first term: `H^n(U ∩ V) →^δ H^{n+1}(X₁) → H^{n+1}(X₂)`. -/
theorem mvExact_ambient (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      ((mvCoSC_shortExact U V hUV).δ n (n + 1) (by simp))
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).f (n + 1))
      ((mvCoSC_shortExact U V hUV).δ_comp n (n + 1) (by simp))).Exact :=
  (mvCoSC_shortExact U V hUV).homology_exact₁ n (n + 1) (by simp)

/-! ## 5. The connecting isomorphism -/

/-- The middle term of the dual Mayer–Vietoris sequence has vanishing `H^n` as soon
as both `H^n(U; F₂)` and `H^n(V; F₂)` vanish.  The biproduct identity
`fst ≫ inl + snd ≫ inr = 𝟙` is carried through the additive dualizing functor and
through `homologyMap`, so the identity of `H^n(X₂)` factors through two zero
objects. -/
theorem isZero_mvCoX2 (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hU : IsZero (Hmod2 (TopCat.of (U : Set X)) n))
    (hV : IsZero (Hmod2 (TopCat.of (V : Set X)) n)) :
    IsZero ((mvCoSC U V hUV).X₂.homology n) := by
  have hU' : IsZero ((dualCx (ZMod 2) (subChainComplex (ZMod 2) X (U : Set X))).homology n) :=
    IsZero.of_iso hU (subCxDualHomologyIso (U : Set X) n)
  have hV' : IsZero ((dualCx (ZMod 2) (subChainComplex (ZMod 2) X (V : Set X))).homology n) :=
    IsZero.of_iso hV (subCxDualHomologyIso (V : Set X) n)
  rw [IsZero.iff_id_eq_zero]
  have htot :
      (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
        (subChainComplex (ZMod 2) X (U : Set X) ⊞ subChainComplex (ZMod 2) X (V : Set X)) ⟶
          (subChainComplex (ZMod 2) X (U : Set X) ⊞ subChainComplex (ZMod 2) X (V : Set X)))
      = 𝟙 _ := biprod.total
  have hid : 𝟙 ((mvCoSC U V hUV).X₂.homology n)
      = HomologicalComplex.homologyMap
            (dualCxFunctor.map (biprod.inl (X := subChainComplex (ZMod 2) X (U : Set X))
              (Y := subChainComplex (ZMod 2) X (V : Set X))).op) n
          ≫ HomologicalComplex.homologyMap (dualCxFunctor.map (biprod.fst
              (X := subChainComplex (ZMod 2) X (U : Set X))
              (Y := subChainComplex (ZMod 2) X (V : Set X))).op) n
        + HomologicalComplex.homologyMap (dualCxFunctor.map (biprod.inr
              (X := subChainComplex (ZMod 2) X (U : Set X))
              (Y := subChainComplex (ZMod 2) X (V : Set X))).op) n
          ≫ HomologicalComplex.homologyMap (dualCxFunctor.map (biprod.snd
              (X := subChainComplex (ZMod 2) X (U : Set X))
              (Y := subChainComplex (ZMod 2) X (V : Set X))).op) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      ← HomologicalComplex.homologyMap_add, ← Functor.map_add, ← op_add, htot]
    simp
  rw [hid, hU'.eq_of_src (HomologicalComplex.homologyMap (dualCxFunctor.map
      (biprod.fst (X := subChainComplex (ZMod 2) X (U : Set X))
        (Y := subChainComplex (ZMod 2) X (V : Set X))).op) n) 0,
    hV'.eq_of_src (HomologicalComplex.homologyMap (dualCxFunctor.map
      (biprod.snd (X := subChainComplex (ZMod 2) X (U : Set X))
        (Y := subChainComplex (ZMod 2) X (V : Set X))).op) n) 0]
  simp

/-- **The Mayer–Vietoris connecting isomorphism.**  If `H^n(U)`, `H^n(V)`,
`H^{n+1}(U)` and `H^{n+1}(V)` all vanish, then
`δ : H^n(U ∩ V; F₂) ≅ H^{n+1}(X; F₂)`. -/
def mvConnectingIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hUn : IsZero (Hmod2 (TopCat.of (U : Set X)) n))
    (hVn : IsZero (Hmod2 (TopCat.of (V : Set X)) n))
    (hUn' : IsZero (Hmod2 (TopCat.of (U : Set X)) (n + 1)))
    (hVn' : IsZero (Hmod2 (TopCat.of (V : Set X)) (n + 1))) :
    Hmod2 (TopCat.of ((U : Set X) ∩ (V : Set X))) n ≅ Hmod2 X (n + 1) :=
  haveI hmono : Mono ((mvCoSC_shortExact U V hUV).δ n (n + 1) (by simp)) :=
    ((mvCoSC_shortExact U V hUV).homology_exact₃ n (n + 1) (by simp)).mono_g
      ((isZero_mvCoX2 U V hUV n hUn hVn).eq_of_src _ _)
  haveI hepi : Epi ((mvCoSC_shortExact U V hUV).δ n (n + 1) (by simp)) :=
    ((mvCoSC_shortExact U V hUV).homology_exact₁ n (n + 1) (by simp)).epi_f
      ((isZero_mvCoX2 U V hUV (n + 1) hUn' hVn').eq_of_tgt _ _)
  haveI : IsIso ((mvCoSC_shortExact U V hUV).δ n (n + 1) (by simp)) :=
    isIso_of_mono_of_epi _
  (mvInterIso U V hUV n).symm
    ≪≫ asIso ((mvCoSC_shortExact U V hUV).δ n (n + 1) (by simp))
    ≪≫ mvAmbientIso U V hUV (n + 1)

end

end GroupApproximation.CharClass
