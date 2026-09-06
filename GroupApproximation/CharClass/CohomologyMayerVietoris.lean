import GroupApproximation.CharClass.CohomologyContractible
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
dualizing with `Hom(-, F₂)` — exact, because `F₂` is an injective module over
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

## Main declarations

* `cohDualFunctor`, `dualCxFunctor`, `dualCx2`, `dualMap2` — the dualization, with
  its exactness and the quasi-isomorphism instance.
* `mvCoSC`, `mvCoSC_shortExact` — the cochain-level short exact sequence.
* `mvInterIso`, `mvAmbientIso` — the two identifications of the outer terms.
* `mvDelta` — the connecting map `H^n(U ∩ V; F₂) ⟶ H^{n+1}(X; F₂)`.
* `mvExact_inter`, `mvExact_sum`, `mvExact_ambient` — exactness at the three spots.
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

/-! ## 1. The dualizing functor and its exactness -/

/-- The dualizing functor `Hom(-, F₂) : (ModuleCat F₂)ᵒᵖ ⥤ ModuleCat F₂`; this is
the functor out of which the vendored `singularCochainComplexFunctor` is built. -/
abbrev cohDualFunctor : (ModuleCat.{0} (ZMod 2))ᵒᵖ ⥤ ModuleCat.{0} (ZMod 2) :=
  (linearYoneda (ZMod 2) (ModuleCat.{0} (ZMod 2))).obj (ModuleCat.of (ZMod 2) (ZMod 2))

instance cohDualFunctor_preservesLimits : PreservesLimits cohDualFunctor :=
  have : PreservesLimits (cohDualFunctor ⋙ forget (ModuleCat.{0} (ZMod 2))) :=
    (inferInstance : PreservesLimits (yoneda.obj (ModuleCat.of (ZMod 2) (ZMod 2))))
  preservesLimits_of_reflects_of_preserves _ (forget _)

/-- `Hom(-, F₂)` turns monomorphisms into epimorphisms: `F₂` is an injective module
over itself (the vendored `moduleInjective_ZMod2`, Baer's criterion over a field). -/
instance cohDualFunctor_preservesEpimorphisms : cohDualFunctor.PreservesEpimorphisms where
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

instance cohDualFunctor_preservesHomology : cohDualFunctor.PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- `cohDualFunctor` is additive: it is `(linearYoneda (ZMod 2) (ModuleCat (ZMod 2))).obj M` for
`M := ModuleCat.of (ZMod 2) (ZMod 2)`, and every object of `linearYoneda` is additive
(`linearYoneda_obj_additive`). Cited directly (via `inferInstanceAs` at the exact pattern the
Mathlib instance is stated for) rather than through generic search, since `PreservesZeroMorphisms`
search on a functor composite has several competing candidate instances
(`isLeftAdjoint`/`isRightAdjoint`/`full`/`additive`) and can fail to find this one. -/
instance cohDualFunctor_additive : cohDualFunctor.Additive :=
  inferInstanceAs (((linearYoneda (ZMod 2) (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).Additive)

/-- The dualizing functor on complexes, `K ↦ Hom(K, F₂)`. -/
abbrev dualCxFunctor : (ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) ⋙
    (cohDualFunctor.mapHomologicalComplex _)

/-- The dual cochain complex of a chain complex. -/
abbrev dualCx2 (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  dualCxFunctor.obj (Opposite.op K)

/-- `dualCxFunctor` is additive: it is a composite of `HomologicalComplex.opFunctor` (additive
whenever the underlying category is preadditive) and the prolongation of the additive
`cohDualFunctor` to homological complexes (`Functor.map_homogical_complex_additive`). Cited
directly at the fully unfolded pattern, for the same reason as `cohDualFunctor_additive`. -/
instance dualCxFunctor_additive : dualCxFunctor.Additive :=
  inferInstanceAs
    ((HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.down ℕ) ⋙
      (cohDualFunctor.mapHomologicalComplex _)).Additive)

/-- `dualCxFunctor` preserves zero morphisms, directly from additivity
(`Functor.preservesZeroMorphisms_of_additive`) rather than generic instance search: search for
`PreservesZeroMorphisms` on a functor composite has several competing candidate instances
(`isLeftAdjoint`/`isRightAdjoint`/`full`/`additive`) and can fail to find this one. -/
instance dualCxFunctor_preservesZeroMorphisms : dualCxFunctor.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive dualCxFunctor

/-- The dual of a chain map. -/
abbrev dualMap2 {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L) :
    dualCx2 L ⟶ dualCx2 K :=
  dualCxFunctor.map f.op

/-- **The dual of a quasi-isomorphism is a quasi-isomorphism** over `F₂`. -/
instance dualMap2_quasiIso {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (dualMap2 f) :=
  inferInstanceAs (QuasiIso ((cohDualFunctor.mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2))
      (ComplexShape.down ℕ)).map f.op)))

/-- `dualMap2` sends identities to identities. Stated and proved once, in isolation, so that
later rewrites can cite it directly rather than fighting `simp`'s matching on the fully
unfolded `dualCxFunctor.map ((𝟙 _).op)` term inside a larger goal. -/
@[simp] theorem dualMap2_id (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :
    dualMap2 (𝟙 K) = 𝟙 (dualCx2 K) := by
  show dualCxFunctor.map (𝟙 K).op = 𝟙 _
  rw [op_id, Functor.map_id]

/-- `dualMap2` is contravariant: dualizing reverses composition. -/
theorem dualMap2_comp {K L M : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) :
    dualMap2 (f ≫ g) = dualMap2 g ≫ dualMap2 f := by
  show dualCxFunctor.map (f ≫ g).op = dualCxFunctor.map g.op ≫ dualCxFunctor.map f.op
  rw [op_comp, Functor.map_comp]

/-- `dualMap2` is additive. -/
theorem dualMap2_add {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f g : K ⟶ L) :
    dualMap2 (f + g) = dualMap2 f + dualMap2 g := by
  show dualCxFunctor.map (f + g).op = dualCxFunctor.map f.op + dualCxFunctor.map g.op
  rw [op_add, Functor.map_add]

/-- The singular cochain complex is the dual of the singular chain complex. -/
theorem cochainCxZMod2_eq_dualCx2 (Y : TopCat.{0}) :
    cochainCxZMod2 Y = dualCx2 (singularChainComplex (ZMod 2) Y) := rfl

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
    cohDualFunctor

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
    dualCx2 (subChainComplex (ZMod 2) X S) ≅ cochainCxZMod2 (TopCat.of S) :=
  dualCxFunctor.mapIso (asIso (subChainCorestrict (ZMod 2) X S)).op

/-- The `H^n` of the dual subordinate-chain complex is `H^n(S; F₂)`. -/
def subCxDualHomologyIso (S : Set X) (n : ℕ) :
    (dualCx2 (subChainComplex (ZMod 2) X S)).homology n ≅ Hmod2 (TopCat.of S) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} (ZMod 2)) (ComplexShape.up ℕ) n).mapIso
    (subCxDualIso S)

/-- The third term of the dual Mayer–Vietoris sequence computes `H^n(U ∩ V; F₂)`. -/
def mvInterIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSC U V hUV).X₃.homology n
      ≅ Hmod2 (TopCat.of (((U : Set X) ∩ (V : Set X) : Set X))) n :=
  subCxDualHomologyIso ((U : Set X) ∩ (V : Set X)) n

/-- The dual of the small-chain inclusion is a quasi-isomorphism, so the first term
of the dual Mayer–Vietoris sequence computes `H^n(X; F₂)`. -/
def mvAmbientIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (mvCoSC U V hUV).X₁.homology n ≅ Hmod2 X n :=
  haveI : IsIso (HomologicalComplex.homologyMap
      (dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  (asIso (HomologicalComplex.homologyMap
    (dualMap2 (smallChainsInclusion (ZMod 2) X (twoSetCover U V hUV))) n)).symm

/-! ## 4. The connecting map and exactness -/

/-- **The Mayer–Vietoris connecting map** `δ : H^n(U ∩ V; F₂) ⟶ H^{n+1}(X; F₂)`. -/
def mvDelta (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (TopCat.of (((U : Set X) ∩ (V : Set X) : Set X))) n ⟶ Hmod2 X (n + 1) :=
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
as both `H^n(U; F₂)` and `H^n(V; F₂)` vanish: the biproduct identity
`fst ≫ inl + snd ≫ inr = 𝟙` is carried through the additive dualizing functor and
through `homologyMap`, so the identity of `H^n(X₂)` is a sum of two maps that each
factor through a zero object. -/
theorem isZero_mvCoX2 (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hU : IsZero (Hmod2 (TopCat.of (U : Set X)) n))
    (hV : IsZero (Hmod2 (TopCat.of (V : Set X)) n)) :
    IsZero ((mvCoSC U V hUV).X₂.homology n) := by
  have hU' : IsZero ((dualCx2 (subChainComplex (ZMod 2) X (U : Set X))).homology n) :=
    IsZero.of_iso hU (subCxDualHomologyIso (U : Set X) n)
  have hV' : IsZero ((dualCx2 (subChainComplex (ZMod 2) X (V : Set X))).homology n) :=
    IsZero.of_iso hV (subCxDualHomologyIso (V : Set X) n)
  have htot :
      (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
        (subChainComplex (ZMod 2) X (U : Set X) ⊞ subChainComplex (ZMod 2) X (V : Set X)) ⟶
          (subChainComplex (ZMod 2) X (U : Set X) ⊞ subChainComplex (ZMod 2) X (V : Set X)))
      = 𝟙 _ := biprod.total
  -- All of the bookkeeping below is phrased purely in terms of `dualCx2`, never
  -- `(mvCoSC U V hUV).X₂` (they are definitionally equal, via `ShortComplex.map`/`.op`
  -- unfolding to `rfl`, but that unfolding is too deep for `rw`/`simp` to see through
  -- reliably); the bridge to the stated goal at the very end is a single `exact`, which
  -- checks the goal at full transparency.
  have key : IsZero ((dualCx2 (subChainComplex (ZMod 2) X (U : Set X) ⊞
      subChainComplex (ZMod 2) X (V : Set X))).homology n) := by
    rw [IsZero.iff_id_eq_zero]
    have hid : 𝟙 ((dualCx2 (subChainComplex (ZMod 2) X (U : Set X) ⊞
        subChainComplex (ZMod 2) X (V : Set X))).homology n)
        = HomologicalComplex.homologyMap (dualMap2
              (biprod.inl (X := subChainComplex (ZMod 2) X (U : Set X))
                (Y := subChainComplex (ZMod 2) X (V : Set X)))) n
            ≫ HomologicalComplex.homologyMap (dualMap2 (biprod.fst
                (X := subChainComplex (ZMod 2) X (U : Set X))
                (Y := subChainComplex (ZMod 2) X (V : Set X)))) n
          + HomologicalComplex.homologyMap (dualMap2 (biprod.inr
                (X := subChainComplex (ZMod 2) X (U : Set X))
                (Y := subChainComplex (ZMod 2) X (V : Set X)))) n
            ≫ HomologicalComplex.homologyMap (dualMap2 (biprod.snd
                (X := subChainComplex (ZMod 2) X (U : Set X))
                (Y := subChainComplex (ZMod 2) X (V : Set X)))) n := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        ← dualMap2_comp, ← dualMap2_comp, ← HomologicalComplex.homologyMap_add,
        ← dualMap2_add, htot, dualMap2_id, HomologicalComplex.homologyMap_id]
    rw [hid, hU'.eq_of_src (HomologicalComplex.homologyMap (dualMap2
        (biprod.fst (X := subChainComplex (ZMod 2) X (U : Set X))
          (Y := subChainComplex (ZMod 2) X (V : Set X)))) n) 0,
      hV'.eq_of_src (HomologicalComplex.homologyMap (dualMap2
        (biprod.snd (X := subChainComplex (ZMod 2) X (U : Set X))
          (Y := subChainComplex (ZMod 2) X (V : Set X)))) n) 0]
    simp
  exact key

/-- **The Mayer–Vietoris connecting isomorphism.**  If `H^n(U)`, `H^n(V)`,
`H^{n+1}(U)` and `H^{n+1}(V)` all vanish, then
`δ : H^n(U ∩ V; F₂) ≅ H^{n+1}(X; F₂)`. -/
def mvConnectingIso (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hUn : IsZero (Hmod2 (TopCat.of (U : Set X)) n))
    (hVn : IsZero (Hmod2 (TopCat.of (V : Set X)) n))
    (hUn' : IsZero (Hmod2 (TopCat.of (U : Set X)) (n + 1)))
    (hVn' : IsZero (Hmod2 (TopCat.of (V : Set X)) (n + 1))) :
    Hmod2 (TopCat.of (((U : Set X) ∩ (V : Set X) : Set X))) n ≅ Hmod2 X (n + 1) :=
  have hij : (ComplexShape.up ℕ).Rel n (n + 1) := by simp
  haveI hmono : Mono ((mvCoSC_shortExact U V hUV).δ n (n + 1) hij) :=
    ((mvCoSC_shortExact U V hUV).homology_exact₃ n (n + 1) hij).mono_g
      ((isZero_mvCoX2 U V hUV n hUn hVn).eq_of_src _ _)
  haveI hepi : Epi ((mvCoSC_shortExact U V hUV).δ n (n + 1) hij) :=
    ((mvCoSC_shortExact U V hUV).homology_exact₁ n (n + 1) hij).epi_f
      ((isZero_mvCoX2 U V hUV (n + 1) hUn' hVn').eq_of_tgt _ _)
  haveI : IsIso ((mvCoSC_shortExact U V hUV).δ n (n + 1) hij) :=
    isIso_of_mono_of_epi _
  (mvInterIso U V hUV n).symm
    ≪≫ asIso ((mvCoSC_shortExact U V hUV).δ n (n + 1) hij)
    ≪≫ mvAmbientIso U V hUV (n + 1)

end

end GroupApproximation.CharClass
