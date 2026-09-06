import GroupApproximation.CharClass.CohomologyBasic
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge

/-!
# The Mayer–Vietoris short exact sequence of cochain complexes

The vendored development carries the Mayer–Vietoris **short exact sequence of chain
complexes** for two opens `U ⊔ V = ⊤`,

```text
0 → C_*(U ∩ V) → C_*(U) ⊕ C_*(V) → C_*^{U,V}(X) → 0,
```

together with an explicit **degreewise splitting** (`mvSplitting`).  A degreewise split
short exact sequence stays short exact under any additive functor, so dualizing with
`Hom(-, F₂)` — exact, because `F₂` is an injective module over itself — gives the short
exact sequence of **cochain** complexes

```text
0 → C^*_{U,V}(X) → C^*(U) ⊕ C^*(V) → C^*(U ∩ V) → 0,
```

whose homology long exact sequence is Mayer–Vietoris.  Two identifications turn the
outer terms into honest cohomology of spaces:

* `C^*(S)` for `S ⊆ X` is the dual of the subordinate-chain complex, because
  `subChainCorestrict` is an **isomorphism** of chain complexes;
* `H^*(C^*_{U,V}(X)) ≅ H^*(X)` because the small-chain inclusion is a
  quasi-isomorphism and the dual of a quasi-isomorphism is a quasi-isomorphism.

Everything lives in the nested namespace `GroupApproximation.CharClass.MV`, so it does
not collide with `cc-cohom-api`'s `CharClass/CohomologyMayerVietoris.lean`, which
develops the same material and whose names are unprefixed.

## Main declarations

* `coDual`, `dualCxFun`, `coCx`, `coMap` — the dualization, with its exactness,
  additivity, and the fact that it preserves quasi-isomorphisms.
* `coSC`, `coSC_shortExact` — the cochain-level short exact sequence.
* `coInterIso`, `coAmbientIso` — the two identifications of the outer terms.
* `coDelta` — the connecting map `H^n(U ∩ V; F₂) ⟶ H^{n+1}(X; F₂)`.
* `coExact_inter`, `coExact_sum`, `coExact_ambient` — exactness at the three spots.

## A trap

`Functor.map_id`, `Functor.map_comp` and `Functor.map_add` must be written with their
`CategoryTheory.` prefix: with `open CategoryTheory` in scope the bare names can still
resolve to the **monadic** `Functor` class, whose `map_id` is `(Functor.map id) = id`
and whose rewrite pattern is `fun x => id <$> x`.
-/

namespace GroupApproximation.CharClass.MV

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.CharClass
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The dualizing functor and its exactness -/

/-- The dualizing functor `Hom(-, F₂) : (ModuleCat F₂)ᵒᵖ ⥤ ModuleCat F₂`. -/
abbrev coDual : (ModuleCat.{0} (ZMod 2))ᵒᵖ ⥤ ModuleCat.{0} (ZMod 2) :=
  (linearYoneda (ZMod 2) (ModuleCat.{0} (ZMod 2))).obj (ModuleCat.of (ZMod 2) (ZMod 2))

instance coDual_preservesLimits : PreservesLimits coDual :=
  have : PreservesLimits (coDual ⋙ forget (ModuleCat.{0} (ZMod 2))) :=
    (inferInstance : PreservesLimits (yoneda.obj (ModuleCat.of (ZMod 2) (ZMod 2))))
  preservesLimits_of_reflects_of_preserves _ (forget _)

/-- `Hom(-, F₂)` turns monomorphisms into epimorphisms: `F₂` is injective over itself. -/
instance coDual_preservesEpimorphisms : coDual.PreservesEpimorphisms where
  preserves {A B} f hf := by
    haveI := hf
    haveI : Mono f.unop := inferInstance
    haveI : Module.Injective (ZMod 2) (ZMod 2) := moduleInjective_ZMod2 (ZMod 2)
    rw [ModuleCat.epi_iff_surjective]
    intro ψ
    obtain ⟨h, hh⟩ := Module.Injective.out (R := ZMod 2) (Q := ZMod 2)
      (f.unop).hom ((ModuleCat.mono_iff_injective f.unop).1 inferInstance) ψ.hom
    refine ⟨ModuleCat.ofHom h, ?_⟩
    show f.unop ≫ ModuleCat.ofHom h = ψ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hh x

instance coDual_preservesHomology : coDual.PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Additivity, cited at the exact pattern the Mathlib instance is stated for: generic
`PreservesZeroMorphisms` search on a functor composite has several competing candidate
instances and can fail to find this one. -/
instance coDual_additive : coDual.Additive :=
  inferInstanceAs (((linearYoneda (ZMod 2) (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).Additive)

/-- The dualizing functor on complexes, `K ↦ Hom(K, F₂)`. -/
abbrev dualCxFun : (ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) ⋙
    (coDual.mapHomologicalComplex _)

/-- The dual cochain complex of a chain complex. -/
abbrev coCx (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  dualCxFun.obj (Opposite.op K)

instance dualCxFun_additive : dualCxFun.Additive :=
  inferInstanceAs
    ((HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) ⋙
      (coDual.mapHomologicalComplex _)).Additive)

instance dualCxFun_preservesZeroMorphisms : dualCxFun.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive dualCxFun

/-- The dual of a chain map. -/
abbrev coMap {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L) : coCx L ⟶ coCx K :=
  dualCxFun.map f.op

/-- **The dual of a quasi-isomorphism is a quasi-isomorphism** over `F₂`. -/
instance coMap_quasiIso {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (coMap f) :=
  inferInstanceAs (QuasiIso ((coDual.mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2))
      (ComplexShape.down ℕ)).map f.op)))

/-! ## 2. Contravariant functoriality, with the `Functor.map_id` trap avoided -/

theorem coMap_comp {K L M : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    coMap g ≫ coMap f = coMap (f ≫ g) := by
  show dualCxFun.map g.op ≫ dualCxFun.map f.op = dualCxFun.map (f ≫ g).op
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp]

theorem coMap_id (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :
    coMap (𝟙 K) = 𝟙 (coCx K) := by
  show dualCxFun.map (𝟙 K).op = 𝟙 _
  rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id]

theorem coMap_add {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f g : K ⟶ L) :
    coMap (f + g) = coMap f + coMap g := by
  show dualCxFun.map (f + g).op = _
  rw [CategoryTheory.op_add, CategoryTheory.Functor.map_add]

theorem coMap_zero {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} :
    coMap (0 : K ⟶ L) = 0 := by
  have h := coMap_add (0 : K ⟶ L) 0
  rw [add_zero] at h
  have h3 : (0 : coCx L ⟶ coCx K) + coMap (0 : K ⟶ L)
      = coMap (0 : K ⟶ L) + coMap (0 : K ⟶ L) := by rw [zero_add, ← h]
  exact ((add_left_inj (coMap (0 : K ⟶ L))).mp h3).symm

/-! ## 3. The Mayer–Vietoris short exact sequence of cochain complexes -/

/-- The Mayer–Vietoris short complex of **cochain** complexes. -/
def coSC (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ShortComplex (CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :=
  dualCxFun.mapShortComplex.obj (mvShortComplex (ZMod 2) U V hUV).op

/-- The degree-`k` piece is split: the vendored chain-level splitting carried through
`op` and the additive dualizing functor. -/
def coSplitting (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (coSC U V hUV)).Splitting :=
  (((mvSplitting (ZMod 2) U V hUV k).ofIso (mvEvalIso (ZMod 2) U V hUV k).symm).op).map coDual

theorem coSC_degreewise_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (coSC U V hUV)).ShortExact :=
  (coSplitting U V hUV k).shortExact

/-- **The Mayer–Vietoris short exact sequence of cochain complexes.** -/
theorem coSC_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) : (coSC U V hUV).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun k => coSC_degreewise_shortExact U V hUV k)

/-! ## 4. Identifying the outer terms -/

/-- For a subspace `S ⊆ X` the dual of the subordinate-chain complex **is** the singular
cochain complex of `S`. -/
def coSubIso (S : Set X) : coCx (subChainComplex (ZMod 2) X S) ≅ cochainCxZMod2 (TopCat.of S) :=
  dualCxFun.mapIso (asIso (subChainCorestrict (ZMod 2) X S)).op

/-- The `H^n` of the dual subordinate-chain complex is `H^n(S; F₂)`. -/
def coSubHomologyIso (S : Set X) (n : ℕ) :
    (coCx (subChainComplex (ZMod 2) X S)).homology n ≅ Hmod2 (TopCat.of S) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) n).mapIso
    (coSubIso S)

/-- The third term computes `H^n(U ∩ V; F₂)`. -/
def coInterIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (coSC U V hUV).X₃.homology n
      ≅ Hmod2 (TopCat.of (((U : Set X) ∩ (V : Set X) : Set X))) n :=
  coSubHomologyIso ((U : Set X) ∩ (V : Set X)) n

/-- The first term computes `H^n(X; F₂)`. -/
def coAmbientIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (coSC U V hUV).X₁.homology n ≅ Hmod2 X n :=
  haveI : IsIso (HomologicalComplex.homologyMap
      (coMap (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  (asIso (HomologicalComplex.homologyMap
    (coMap (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n)).symm

/-! ## 5. The connecting map and exactness -/

/-- **The Mayer–Vietoris connecting map** `δ : H^n(U ∩ V; F₂) ⟶ H^{n+1}(X; F₂)`. -/
def coDelta (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (TopCat.of (((U : Set X) ∩ (V : Set X) : Set X))) n ⟶ Hmod2 X (n + 1) :=
  (coInterIso U V hUV n).inv
    ≫ (coSC_shortExact U V hUV).δ n (n + 1) (by simp)
    ≫ (coAmbientIso U V hUV (n + 1)).hom

/-- Exactness at `H^n` of the third term. -/
theorem coExact_inter (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (coSC U V hUV).g n)
      ((coSC_shortExact U V hUV).δ n (n + 1) (by simp))
      ((coSC_shortExact U V hUV).comp_δ n (n + 1) (by simp))).Exact :=
  (coSC_shortExact U V hUV).homology_exact₃ n (n + 1) (by simp)

/-- Exactness at the middle term. -/
theorem coExact_sum (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (coSC U V hUV).f n)
      (HomologicalComplex.homologyMap (coSC U V hUV).g n)
      (by rw [← HomologicalComplex.homologyMap_comp, (coSC U V hUV).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (coSC_shortExact U V hUV).homology_exact₂ n

/-- Exactness at `H^{n+1}` of the first term. -/
theorem coExact_ambient (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      ((coSC_shortExact U V hUV).δ n (n + 1) (by simp))
      (HomologicalComplex.homologyMap (coSC U V hUV).f (n + 1))
      ((coSC_shortExact U V hUV).δ_comp n (n + 1) (by simp))).Exact :=
  (coSC_shortExact U V hUV).homology_exact₁ n (n + 1) (by simp)

end

end GroupApproximation.CharClass.MV
