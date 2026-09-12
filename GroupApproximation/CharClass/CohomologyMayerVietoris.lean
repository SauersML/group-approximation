import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.CharClass.CoeffField
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris

/-!
# Mayer–Vietoris for singular cohomology, over any coefficient field

The vendored development carries the Mayer–Vietoris **short exact sequence of
chain complexes** for two opens `U ⊔ V = ⊤`,

```text
0 → C_*(U ∩ V) → C_*(U) ⊕ C_*(V) → C_*^{U,V}(X) → 0,
```

together with an explicit **degreewise splitting** (`mvSplitting`).  A degreewise
split short exact sequence stays short exact under any additive functor, so
dualizing with `Hom(-, K)` — exact, because a field is an injective module over
itself — gives the short exact sequence of **cochain** complexes

```text
0 → C^*_{U,V}(X) → C^*(U) ⊕ C^*(V) → C^*(U ∩ V) → 0,
```

whose homology long exact sequence is Mayer–Vietoris.  Two identifications turn
the outer terms into honest cohomology of spaces:

* `C^*(S)` for `S ⊆ X` is the dual of the subordinate-chain complex, because
  `subChainCorestrict` is an **isomorphism** of chain complexes;
* `H^*(C^*_{U,V}(X)) ≅ H^*(X)` because the small-chain inclusion is a
  quasi-isomorphism and the dual of a quasi-isomorphism is a quasi-isomorphism.

## The coefficient parameter

Every vendored input here is already generic in the coefficient ring: the MV
chain-level sequence, its splitting, the subordinate and small chain complexes
and their comparison maps all take `(R : Type) [CommRing R]`, and the chain-level
map is already `biprod.lift ι (-ι')`, **with the minus sign**.  So this file is a
substitution, with exactly one genuine input to supply: the coefficient must be
an injective module over itself, which at `F₂` is the vendored
`moduleInjective_ZMod2` and in general is `moduleInjective_of_field`
(`CoeffField.lean`).

`[CommRing K]` suffices for the dualizing functor and the dual complex;
`[Field K]` is asked for exactly where injectivity is used, and everything
downstream of it.

**Naming.**  The generic declarations carry an `Of` suffix and take the
coefficient as an explicit first argument, because none of them has an argument
that would determine it — `mvCoSC U V hUV` mentions only two opens.  The `F₂`
names are `abbrev`s at `K = ZMod 2`, hence reducible, so every existing consumer
elaborates unchanged and the generic instances below fire on the `F₂` spellings.

## Main declarations

* `cohDualFunctorOf`, `dualCxFunctorOf`, `dualCxOf`, `dualMapOf` — the
  dualization, with its exactness and the quasi-isomorphism instance.
* `mvCoSCOf`, `mvCoSCOf_shortExact` — the cochain-level short exact sequence.
* `mvInterIsoOf`, `mvAmbientIsoOf` — the two identifications of the outer terms.
* `mvDeltaOf` — the connecting map `H^n(U ∩ V; K) ⟶ H^{n+1}(X; K)`.
* `mvExactOf_inter`, `mvExactOf_sum`, `mvExactOf_ambient` — exactness at the three spots.
* `isZero_mvCoX2Of` — the middle term vanishes when both `H^n(U)` and `H^n(V)` do.
* `mvConnectingIsoOf` — `H^n(U ∩ V; K) ≅ H^{n+1}(X; K)` when `U` and `V` have
  vanishing cohomology in degrees `n` and `n+1`.
* `cohDualFunctor`, `dualCx2`, `dualMap2`, `mvCoSC`, `mvDelta`, … — the `F₂`
  instances, with the names the rest of the tree already uses.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The dualizing functor and its exactness -/

/-- The dualizing functor `Hom(-, K) : (ModuleCat K)ᵒᵖ ⥤ ModuleCat K`; this is
the functor out of which the vendored `singularCochainComplexFunctor` is built. -/
abbrev cohDualFunctorOf (K : Type) [CommRing K] :
    (ModuleCat.{0} K)ᵒᵖ ⥤ ModuleCat.{0} K :=
  (linearYoneda K (ModuleCat.{0} K)).obj (ModuleCat.of K K)

instance cohDualFunctorOf_preservesLimits (K : Type) [CommRing K] :
    PreservesLimits (cohDualFunctorOf K) :=
  have : PreservesLimits (cohDualFunctorOf K ⋙ forget (ModuleCat.{0} K)) :=
    (inferInstance : PreservesLimits (yoneda.obj (ModuleCat.of K K)))
  preservesLimits_of_reflects_of_preserves _ (forget _)

/-- `Hom(-, K)` turns monomorphisms into epimorphisms: a field is an injective
module over itself (`moduleInjective_of_field`). -/
instance cohDualFunctorOf_preservesEpimorphisms (K : Type) [Field K] :
    (cohDualFunctorOf K).PreservesEpimorphisms where
  preserves {A B} f hf := by
    haveI := hf
    haveI : Mono f.unop := inferInstance
    haveI : Module.Injective K K := moduleInjective_of_field K K
    rw [ModuleCat.epi_iff_surjective]
    intro ψ
    obtain ⟨h, hh⟩ := Module.Injective.out (R := K) (Q := K)
      (f.unop).hom ((ModuleCat.mono_iff_injective f.unop).1 inferInstance) ψ.hom
    refine ⟨ModuleCat.ofHom h, ?_⟩
    show f.unop ≫ ModuleCat.ofHom h = ψ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hh x

instance cohDualFunctorOf_preservesHomology (K : Type) [Field K] :
    (cohDualFunctorOf K).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The dualizing functor on complexes, `C ↦ Hom(C, K)`. -/
abbrev dualCxFunctorOf (K : Type) [CommRing K] :
    (ChainComplex (ModuleCat.{0} K) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} K) ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{0} K) (ComplexShape.down ℕ) ⋙
    (cohDualFunctorOf K).mapHomologicalComplex (ComplexShape.down ℕ).symm

instance dualCxFunctorOf_additive (K : Type) [CommRing K] :
    (dualCxFunctorOf K).Additive where
  map_add {C D f g} := by
    show ((cohDualFunctorOf K).mapHomologicalComplex (ComplexShape.down ℕ).symm).map
        ((HomologicalComplex.opFunctor (ModuleCat.{0} K)
          (ComplexShape.down ℕ)).map (f + g)) = _
    rw [Functor.map_add, Functor.map_add]
    rfl

/-- The dual cochain complex of a chain complex. -/
abbrev dualCxOf (K : Type) [CommRing K] (C : ChainComplex (ModuleCat.{0} K) ℕ) :
    CochainComplex (ModuleCat.{0} K) ℕ :=
  (dualCxFunctorOf K).obj (Opposite.op C)

/-- The dual of a chain map. -/
abbrev dualMapOf (K : Type) [CommRing K] {C D : ChainComplex (ModuleCat.{0} K) ℕ}
    (f : C ⟶ D) : dualCxOf K D ⟶ dualCxOf K C :=
  (dualCxFunctorOf K).map f.op

/-- **The dual of a quasi-isomorphism is a quasi-isomorphism** over a field. -/
instance dualMapOf_quasiIso (K : Type) [Field K]
    {C D : ChainComplex (ModuleCat.{0} K) ℕ} (f : C ⟶ D) [QuasiIso f] :
    QuasiIso (dualMapOf K f) :=
  inferInstanceAs (QuasiIso
    (((cohDualFunctorOf K).mapHomologicalComplex (ComplexShape.down ℕ).symm).map
      ((HomologicalComplex.opFunctor (ModuleCat.{0} K)
        (ComplexShape.down ℕ)).map f.op)))

/-- The singular cochain complex is the dual of the singular chain complex. -/
theorem cochainCxK_eq_dualCxOf (K : Type) [CommRing K] (Y : TopCat.{0}) :
    cochainCxK K Y = dualCxOf K (singularChainComplex K Y) := rfl

/-- The relation `n ⇝ n+1` of the cochain complex shape. -/
theorem upRel (n : ℕ) : (ComplexShape.up ℕ).Rel n (n + 1) := rfl

/-! ## 2. The Mayer–Vietoris short exact sequence of cochain complexes -/

/-- The Mayer–Vietoris short complex of **cochain** complexes: the `Hom(-, K)`
dual of the vendored chain-level Mayer–Vietoris short complex. -/
def mvCoSCOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ShortComplex (CochainComplex (ModuleCat.{0} K) ℕ) where
  X₁ := dualCxOf K (twoOpenCoverSmallChains K U V hUV)
  X₂ := dualCxOf K (subChainComplex K X (U : Set X) ⊞ subChainComplex K X (V : Set X))
  X₃ := dualCxOf K (subChainComplex K X ((U : Set X) ∩ (V : Set X)))
  f := dualMapOf K (mvRightChainMap K U V hUV)
  g := dualMapOf K (mvLeftChainMap K U V hUV)
  zero := by
    show (dualCxFunctorOf K).map (mvRightChainMap K U V hUV).op ≫
        (dualCxFunctorOf K).map (mvLeftChainMap K U V hUV).op = 0
    rw [← Functor.map_comp, ← op_comp, mvLeft_comp_mvRight]
    simp only [op_zero, Functor.map_zero]

/-- The splitting of the degree-`k` piece of the dual short complex, obtained from
the vendored chain-level splitting `mvSplitting` by `op` and the additive
dualizing functor.  The two short complexes are definitionally equal, so the
fields transfer verbatim. -/
def mvCoSplittingAuxOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    (((HomologicalComplex.eval (ModuleCat.{0} K) (ComplexShape.down ℕ) k).mapShortComplex.obj
      (mvShortComplex K U V hUV)).op.map (cohDualFunctorOf K)).Splitting :=
  (((mvSplitting K U V hUV k).ofIso
    (mvEvalIso K U V hUV k).symm).op).map (cohDualFunctorOf K)

/-- The degree-`k` piece of the dual Mayer–Vietoris short complex is split. -/
def mvCoSplittingOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} K) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (mvCoSCOf K U V hUV)).Splitting where
  r := (mvCoSplittingAuxOf K U V hUV k).r
  s := (mvCoSplittingAuxOf K U V hUV k).s
  f_r := (mvCoSplittingAuxOf K U V hUV k).f_r
  s_g := (mvCoSplittingAuxOf K U V hUV k).s_g
  id := (mvCoSplittingAuxOf K U V hUV k).id

theorem mvCoSCOf_degreewise_shortExact (K : Type) [CommRing K] (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} K) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (mvCoSCOf K U V hUV)).ShortExact :=
  (mvCoSplittingOf K U V hUV k).shortExact

/-- **The Mayer–Vietoris short exact sequence of cochain complexes.** -/
theorem mvCoSCOf_shortExact (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSCOf K U V hUV).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun k => mvCoSCOf_degreewise_shortExact K U V hUV k)

/-! ## 3. Identifying the outer terms -/

/-- For a subspace `S ⊆ X` the dual of the subordinate-chain complex **is** the
singular cochain complex of `S`: the corestriction of the inclusion is an
isomorphism of chain complexes. -/
def subCxDualIsoOf (K : Type) [CommRing K] (S : Set X) :
    dualCxOf K (subChainComplex K X S) ≅ cochainCxK K (TopCat.of S) :=
  (dualCxFunctorOf K).mapIso (asIso (subChainCorestrict K X S)).op

/-- The `H^n` of the dual subordinate-chain complex is `H^n(S; K)`. -/
def subCxDualHomologyIsoOf (K : Type) [CommRing K] (S : Set X) (n : ℕ) :
    (dualCxOf K (subChainComplex K X S)).homology n ≅ Hmod K (TopCat.of S) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} K) (ComplexShape.up ℕ) n).mapIso
    (subCxDualIsoOf K S)

/-- The third term of the dual Mayer–Vietoris sequence computes `H^n(U ∩ V; K)`. -/
def mvInterIsoOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSCOf K U V hUV).X₃.homology n
      ≅ Hmod K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n :=
  subCxDualHomologyIsoOf K ((U : Set X) ∩ (V : Set X)) n

/-- The dual of the small-chain inclusion is a quasi-isomorphism, so the first term
of the dual Mayer–Vietoris sequence computes `H^n(X; K)`. -/
def mvAmbientIsoOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSCOf K U V hUV).X₁.homology n ≅ Hmod K X n :=
  haveI : IsIso (HomologicalComplex.homologyMap
      (dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  (asIso (HomologicalComplex.homologyMap
    (dualMapOf K (smallChainsInclusion K X (twoSetCover U V hUV))) n)).symm

/-! ## 4. The connecting map and exactness -/

/-- **The Mayer–Vietoris connecting map** `δ : H^n(U ∩ V; K) ⟶ H^{n+1}(X; K)`. -/
def mvDeltaOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n ⟶ Hmod K X (n + 1) :=
  (mvInterIsoOf K U V hUV n).inv
    ≫ (mvCoSCOf_shortExact K U V hUV).δ n (n + 1) (upRel n)
    ≫ (mvAmbientIsoOf K U V hUV (n + 1)).hom

/-- Exactness at `H^n` of the third term: `H^n(X₂) → H^n(U ∩ V) →^δ H^{n+1}(X₁)`. -/
theorem mvExactOf_inter (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n)
      ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) (upRel n))
      ((mvCoSCOf_shortExact K U V hUV).comp_δ n (n + 1) (upRel n))).Exact :=
  (mvCoSCOf_shortExact K U V hUV).homology_exact₃ n (n + 1) (upRel n)

/-- Exactness at the middle term: `H^n(X₁) → H^n(X₂) → H^n(X₃)`. -/
theorem mvExactOf_sum (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f n)
      (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).g n)
      (by rw [← HomologicalComplex.homologyMap_comp, (mvCoSCOf K U V hUV).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (mvCoSCOf_shortExact K U V hUV).homology_exact₂ n

/-- Exactness at `H^{n+1}` of the first term: `H^n(U ∩ V) →^δ H^{n+1}(X₁) → H^{n+1}(X₂)`. -/
theorem mvExactOf_ambient (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) (upRel n))
      (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f (n + 1))
      ((mvCoSCOf_shortExact K U V hUV).δ_comp n (n + 1) (upRel n))).Exact :=
  (mvCoSCOf_shortExact K U V hUV).homology_exact₁ n (n + 1) (upRel n)

/-! ## 5. The connecting isomorphism -/

/-- The middle term of the dual Mayer–Vietoris sequence has vanishing `H^n` as soon
as both `H^n(U; K)` and `H^n(V; K)` vanish: the biproduct identity
`fst ≫ inl + snd ≫ inr = 𝟙` is carried through the additive dualizing functor and
through `homologyMap`, so the identity of `H^n(X₂)` is a sum of two maps that each
factor through a zero object. -/
theorem isZero_mvCoX2Of (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hU : IsZero (Hmod K (TopCat.of (U : Set X)) n))
    (hV : IsZero (Hmod K (TopCat.of (V : Set X)) n)) :
    IsZero ((mvCoSCOf K U V hUV).X₂.homology n) := by
  have hU' : IsZero ((dualCxOf K (subChainComplex K X (U : Set X))).homology n) :=
    IsZero.of_iso hU (subCxDualHomologyIsoOf K (U : Set X) n)
  have hV' : IsZero ((dualCxOf K (subChainComplex K X (V : Set X))).homology n) :=
    IsZero.of_iso hV (subCxDualHomologyIsoOf K (V : Set X) n)
  rw [IsZero.iff_id_eq_zero]
  have htot :
      (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
        (subChainComplex K X (U : Set X) ⊞ subChainComplex K X (V : Set X)) ⟶
          (subChainComplex K X (U : Set X) ⊞ subChainComplex K X (V : Set X)))
      = 𝟙 _ := biprod.total
  have hid : 𝟙 ((mvCoSCOf K U V hUV).X₂.homology n)
      = HomologicalComplex.homologyMap (dualMapOf K
            (biprod.inl (X := subChainComplex K X (U : Set X))
              (Y := subChainComplex K X (V : Set X)))) n
          ≫ HomologicalComplex.homologyMap (dualMapOf K (biprod.fst
              (X := subChainComplex K X (U : Set X))
              (Y := subChainComplex K X (V : Set X)))) n
        + HomologicalComplex.homologyMap (dualMapOf K (biprod.inr
              (X := subChainComplex K X (U : Set X))
              (Y := subChainComplex K X (V : Set X)))) n
          ≫ HomologicalComplex.homologyMap (dualMapOf K (biprod.snd
              (X := subChainComplex K X (U : Set X))
              (Y := subChainComplex K X (V : Set X)))) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      ← HomologicalComplex.homologyMap_add, ← Functor.map_add, ← op_add, htot, op_id]
    rw [(dualCxFunctorOf K).map_id]
    exact (HomologicalComplex.homologyMap_id _ n).symm
  rw [hid, hU'.eq_of_src (HomologicalComplex.homologyMap (dualMapOf K
      (biprod.fst (X := subChainComplex K X (U : Set X))
        (Y := subChainComplex K X (V : Set X)))) n) 0,
    hV'.eq_of_src (HomologicalComplex.homologyMap (dualMapOf K
      (biprod.snd (X := subChainComplex K X (U : Set X))
        (Y := subChainComplex K X (V : Set X)))) n) 0,
    comp_zero, comp_zero, add_zero]
  rfl

/-- **The Mayer–Vietoris connecting isomorphism.**  If `H^n(U)`, `H^n(V)`,
`H^{n+1}(U)` and `H^{n+1}(V)` all vanish, then
`δ : H^n(U ∩ V; K) ≅ H^{n+1}(X; K)`. -/
def mvConnectingIsoOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hUn : IsZero (Hmod K (TopCat.of (U : Set X)) n))
    (hVn : IsZero (Hmod K (TopCat.of (V : Set X)) n))
    (hUn' : IsZero (Hmod K (TopCat.of (U : Set X)) (n + 1)))
    (hVn' : IsZero (Hmod K (TopCat.of (V : Set X)) (n + 1))) :
    Hmod K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n ≅ Hmod K X (n + 1) :=
  haveI : Mono ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) (upRel n)) :=
    ((mvCoSCOf_shortExact K U V hUV).homology_exact₃ n (n + 1) (upRel n)).mono_g
      ((isZero_mvCoX2Of K U V hUV n hUn hVn).eq_of_src _ _)
  haveI : Epi ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) (upRel n)) :=
    ((mvCoSCOf_shortExact K U V hUV).homology_exact₁ n (n + 1) (upRel n)).epi_f
      ((isZero_mvCoX2Of K U V hUV (n + 1) hUn' hVn').eq_of_tgt _ _)
  haveI : IsIso ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) (upRel n)) :=
    isIso_of_mono_of_epi _
  (mvInterIsoOf K U V hUV n).symm
    ≪≫ asIso ((mvCoSCOf_shortExact K U V hUV).δ n (n + 1) (upRel n))
    ≪≫ mvAmbientIsoOf K U V hUV (n + 1)

/-! ## 6. The `F₂` instance

The names the rest of the tree uses.  Each is an `abbrev` at `K = ZMod 2`, hence
reducible, so every existing consumer elaborates unchanged and the generic
instances above fire on these spellings without restating them. -/

/-- `Hom(-, F₂)`. -/
abbrev cohDualFunctor : (ModuleCat.{0} (ZMod 2))ᵒᵖ ⥤ ModuleCat.{0} (ZMod 2) :=
  cohDualFunctorOf (ZMod 2)

/-- `Hom(-, F₂)` on complexes. -/
abbrev dualCxFunctor : (ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  dualCxFunctorOf (ZMod 2)

/-- The dual cochain complex of a chain complex, over `F₂`. -/
abbrev dualCx2 (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  dualCxOf (ZMod 2) C

/-- The dual of a chain map, over `F₂`. -/
abbrev dualMap2 {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : C ⟶ D) :
    dualCx2 D ⟶ dualCx2 C :=
  dualMapOf (ZMod 2) f

/-- The singular `F₂`-cochain complex is the dual of the singular chain complex. -/
theorem cochainCxZMod2_eq_dualCx2 (Y : TopCat.{0}) :
    cochainCxZMod2 Y = dualCx2 (singularChainComplex (ZMod 2) Y) := rfl

/-- The mod-2 Mayer–Vietoris short complex of cochain complexes. -/
abbrev mvCoSC (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ShortComplex (CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :=
  mvCoSCOf (ZMod 2) U V hUV

abbrev mvCoSplittingAux (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :=
  mvCoSplittingAuxOf (ZMod 2) U V hUV k

abbrev mvCoSplitting (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (mvCoSC U V hUV)).Splitting :=
  mvCoSplittingOf (ZMod 2) U V hUV k

theorem mvCoSC_degreewise_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) (k : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) k).mapShortComplex.obj
      (mvCoSC U V hUV)).ShortExact :=
  mvCoSCOf_degreewise_shortExact (ZMod 2) U V hUV k

theorem mvCoSC_shortExact (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    (mvCoSC U V hUV).ShortExact :=
  mvCoSCOf_shortExact (ZMod 2) U V hUV

abbrev subCxDualIso (S : Set X) :
    dualCx2 (subChainComplex (ZMod 2) X S) ≅ cochainCxZMod2 (TopCat.of S) :=
  subCxDualIsoOf (ZMod 2) S

abbrev subCxDualHomologyIso (S : Set X) (n : ℕ) :
    (dualCx2 (subChainComplex (ZMod 2) X S)).homology n ≅ Hmod2 (TopCat.of S) n :=
  subCxDualHomologyIsoOf (ZMod 2) S n

abbrev mvInterIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSC U V hUV).X₃.homology n
      ≅ Hmod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n :=
  mvInterIsoOf (ZMod 2) U V hUV n

abbrev mvAmbientIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSC U V hUV).X₁.homology n ≅ Hmod2 X n :=
  mvAmbientIsoOf (ZMod 2) U V hUV n

/-- **The mod-2 Mayer–Vietoris connecting map.** -/
abbrev mvDelta (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n ⟶ Hmod2 X (n + 1) :=
  mvDeltaOf (ZMod 2) U V hUV n

theorem mvExact_inter (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).g n)
      ((mvCoSC_shortExact U V hUV).δ n (n + 1) (upRel n))
      ((mvCoSC_shortExact U V hUV).comp_δ n (n + 1) (upRel n))).Exact :=
  mvExactOf_inter (ZMod 2) U V hUV n

theorem mvExact_sum (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).f n)
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).g n)
      (by rw [← HomologicalComplex.homologyMap_comp, (mvCoSC U V hUV).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  mvExactOf_sum (ZMod 2) U V hUV n

theorem mvExact_ambient (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk
      ((mvCoSC_shortExact U V hUV).δ n (n + 1) (upRel n))
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).f (n + 1))
      ((mvCoSC_shortExact U V hUV).δ_comp n (n + 1) (upRel n))).Exact :=
  mvExactOf_ambient (ZMod 2) U V hUV n

theorem isZero_mvCoX2 (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hU : IsZero (Hmod2 (TopCat.of (U : Set X)) n))
    (hV : IsZero (Hmod2 (TopCat.of (V : Set X)) n)) :
    IsZero ((mvCoSC U V hUV).X₂.homology n) :=
  isZero_mvCoX2Of (ZMod 2) U V hUV n hU hV

/-- **The mod-2 Mayer–Vietoris connecting isomorphism.** -/
abbrev mvConnectingIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hUn : IsZero (Hmod2 (TopCat.of (U : Set X)) n))
    (hVn : IsZero (Hmod2 (TopCat.of (V : Set X)) n))
    (hUn' : IsZero (Hmod2 (TopCat.of (U : Set X)) (n + 1)))
    (hVn' : IsZero (Hmod2 (TopCat.of (V : Set X)) (n + 1))) :
    Hmod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n ≅ Hmod2 X (n + 1) :=
  mvConnectingIsoOf (ZMod 2) U V hUV n hUn hVn hUn' hVn'

end

end GroupApproximation.CharClass
