import GroupApproximation.CharClass.RelativeSmallChains
import GroupApproximation.CharClass.RelativeFunctorial

/-!
# Excision for an open cover

Let `U, V` be open subsets of `X` with `U ∪ V = X`.  **Excision** says that the
inclusion of pairs `(V, U ∩ V) → (X, U)` induces an isomorphism

```text
H^n(X, U; F₂) ≅ H^n(V, U ∩ V; F₂).
```

The proof here is short because everything has been arranged so that the only
geometric input is the vendored small-simplices theorem.  Restricting a cochain of
`X` to the subspace `V` sends `C^*(X, U)` to `C^*(V, U ∩ V)`; that map is

* **surjective**, because the singular chains of `X` supported in `V` split off as a
  coordinate subspace of the free chain group (`relRetract`), and
* has **kernel** exactly the cochains vanishing on both the `U`-supported and the
  `V`-supported chains, i.e. on all `{U, V}`-small chains,

and the complex of cochains vanishing on all small chains is acyclic
(`smallAnnComplex_acyclic`).  The long exact sequence of the resulting short exact
sequence then makes the restriction a quasi-isomorphism.

The subspace `U ∩ V` of `V` is written `excisedSub U V`, the preimage of `U` under
the inclusion `V ↪ X`.

## Main results

* `excisionShortExact` — `0 → smallAnn → C^*(X, U) → C^*(V, U ∩ V) → 0`.
* `isIso_excision` — the excision isomorphism, as `IsIso` of `relPullback`.
* `excisionIso` — the same, bundled.
-/

open CategoryTheory Limits AlgebraicTopology TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

open Classical

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. The subspace `U ∩ V` of `V`, and small simplices of the two-set cover -/

/-- The subset `U ∩ V` of `X`, seen inside the subspace `V`. -/
def excisedSub (U V : Set X) : Set (TopCat.of V) :=
  (ConcreteCategory.hom (sInclusion V)) ⁻¹' U

theorem isSmallSimplex_of_subordinate_left (U V : Opens X) (hUV : U ⊔ V = ⊤) {n : ℕ}
    {σ : singularSimplices X n} (hσ : IsSubordinate (U : Set X) σ) :
    IsSmallSimplex (twoSetCover U V hUV) σ :=
  hσ.isSmallSimplex (twoSetCover_memU U V hUV)

theorem isSmallSimplex_of_subordinate_right (U V : Opens X) (hUV : U ⊔ V = ⊤) {n : ℕ}
    {σ : singularSimplices X n} (hσ : IsSubordinate (V : Set X) σ) :
    IsSmallSimplex (twoSetCover U V hUV) σ :=
  hσ.isSmallSimplex (twoSetCover_memV U V hUV)

theorem subordinate_or_of_isSmallSimplex (U V : Opens X) (hUV : U ⊔ V = ⊤) {n : ℕ}
    {σ : singularSimplices X n} (hσ : IsSmallSimplex (twoSetCover U V hUV) σ) :
    IsSubordinate (U : Set X) σ ∨ IsSubordinate (V : Set X) σ := by
  obtain ⟨S, hS, h⟩ := hσ
  rcases hS with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

/-! ## 2. Two lemmas about the chain-level retraction -/

/-- The retraction sends the basis chain of a pushed-forward simplex back to the
basis chain of that simplex. -/
theorem relRetract_generator (A : Set X) (n : ℕ) (τ : singularSimplices (TopCat.of A) n) :
    (relRetract R X A n).hom (chainGenerator R X n (pushSimplex (sInclusion A) n τ))
      = chainGenerator R (TopCat.of A) n τ := by
  have h1 : (relRetract R X A n).hom
      ((singularChainMap R (sInclusion A) n).hom (chainGenerator R (TopCat.of A) n τ))
      = chainGenerator R (TopCat.of A) n τ :=
    congrArg
      (fun f : singularChainGroup R (TopCat.of A) n ⟶ singularChainGroup R (TopCat.of A) n =>
        f.hom (chainGenerator R (TopCat.of A) n τ))
      (singularChainMap_comp_relRetract A n)
  rwa [singularChainMap_generator] at h1

/-- The retraction kills the basis chain of a simplex not supported in `A`. -/
theorem relRetract_generator_of_not (A : Set X) (n : ℕ) {σ : singularSimplices X n}
    (hσ : ¬ IsSubordinate A σ) :
    (relRetract R X A n).hom (chainGenerator R X n σ) = 0 := by
  have h : Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ
      ≫ subKeep R X A n = subKeepComp R X A n σ := Sigma.ι_desc _ _
  have h3 : subKeepComp R X A n σ = 0 := by
    unfold subKeepComp
    rw [dif_neg hσ]
  rw [h3] at h
  have h2 := congrArg
    (fun f : ModuleCat.of R R ⟶ ModuleCat.of R (subChainSubmodule R X A n) => f.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h4 : (subKeep R X A n).hom (chainGenerator R X n σ) = 0 := by
    refine h2.trans ?_
    rfl
  have h5 : (subKeepAt R X A n).hom (chainGenerator R X n σ) = 0 := h4
  show (subChainCorestrictInv R X A n).hom ((subKeepAt R X A n).hom (chainGenerator R X n σ)) = 0
  rw [h5, map_zero]

/-- A simplex of the subspace `V` whose image in `X` lies in `U` is a simplex of the
subspace `V` supported in `U ∩ V`. -/
theorem isSubordinate_excisedSub (U V : Set X) (n : ℕ)
    (τ : singularSimplices (TopCat.of V) n)
    (h : IsSubordinate U (pushSimplex (sInclusion V) n τ)) :
    IsSubordinate (excisedSub U V) τ := by
  have h2 : Set.range (singularSimplexAsContinuousMap X n
      (pushSimplex (sInclusion V) n τ)) ⊆ U := h
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  have h3 := h2 (Set.mem_range_self t)
  rw [pushSimplex_continuousMap (sInclusion V) n τ] at h3
  show (ConcreteCategory.hom (sInclusion V)) (mvSimplexMap τ t) ∈ U
  simpa only [ContinuousMap.comp_apply] using h3

/-! ## 3. The excision short exact sequence -/

variable (U V : Opens X) (hUV : U ⊔ V = ⊤)

/-- The map of pairs `(V, U ∩ V) → (X, U)` is the inclusion of the subspace `V`. -/
theorem excision_mapsTo :
    ∀ x ∈ excisedSub (U : Set X) (V : Set X),
      (ConcreteCategory.hom (sInclusion (V : Set X))) x ∈ (U : Set X) :=
  fun _ hx => hx

/-- Restriction of relative cochains along `(V, U ∩ V) → (X, U)`. -/
def excisionCochainMap (R : Type) [CommRing R] :
    relCochainComplex R X (U : Set X) ⟶
      relCochainComplex R (TopCat.of (V : Set X)) (excisedSub (U : Set X) (V : Set X)) :=
  relCochainMap R (sInclusion (V : Set X)) (excision_mapsTo U V)

theorem smallAnn_le_rel (R : Type) [CommRing R] (n : ℕ) :
    smallAnnSubmodule R X (twoSetCover U V hUV) n ≤ relCochainSubmodule R X (U : Set X) n :=
  fun _ hφ σ hσ => hφ σ (isSmallSimplex_of_subordinate_left U V hUV hσ)

/-- The inclusion of the small-annihilator complex into the relative cochains of
`(X, U)`. -/
def smallAnnToRel (R : Type) [CommRing R] :
    smallAnnComplex R X (twoSetCover U V hUV) ⟶ relCochainComplex R X (U : Set X) where
  f n := ModuleCat.ofHom (Submodule.inclusion (smallAnn_le_rel U V hUV R n))
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    rw [smallAnnComplex_d, relCochainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

theorem smallAnnToRel_comp (R : Type) [CommRing R] :
    smallAnnToRel U V hUV R ≫ excisionCochainMap U V R = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have key : ∀ ψ : smallAnnSubmodule R X (twoSetCover U V hUV) n,
      cochainPullback (sInclusion (V : Set X)) n (ψ : singularCochainGroup R X n) = 0 := by
    intro ψ
    apply cochain_ext
    intro τ
    rw [cochainPullback_eval, cochainEval_zero]
    exact ψ.2 _ (isSmallSimplex_of_subordinate_right U V hUV
      (isSubordinate_pushSimplex_sInclusion (V : Set X) n τ))
  exact Subtype.ext (key φ)

/-- The excision short complex `smallAnn → C^*(X, U) → C^*(V, U ∩ V)`. -/
def excisionShortComplex (R : Type) [CommRing R] :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk (smallAnnToRel U V hUV R) (excisionCochainMap U V R)
    (smallAnnToRel_comp U V hUV R)

/-- The candidate preimage of a relative cochain of `(V, U ∩ V)`: extend it by zero
off the chains supported in `V`. -/
theorem excisionCochainMap_preimage (R : Type) [CommRing R] (n : ℕ)
    (χ : relCochainSubmodule R (TopCat.of (V : Set X))
      (excisedSub (U : Set X) (V : Set X)) n) :
    (relRetract R X (V : Set X) n
        ≫ (χ : singularCochainGroup R (TopCat.of (V : Set X)) n))
      ∈ relCochainSubmodule R X (U : Set X) n := by
  intro σ hσ
  show ((relRetract R X (V : Set X) n
    ≫ (χ : singularCochainGroup R (TopCat.of (V : Set X)) n)).hom)
      (chainGenerator R X n σ) = 0
  rw [ModuleCat.comp_apply]
  by_cases hV : IsSubordinate (V : Set X) σ
  · obtain ⟨τ, rfl⟩ := exists_pushSimplex_of_subordinate (V : Set X) n hV
    rw [relRetract_generator]
    exact χ.2 τ (isSubordinate_excisedSub (U : Set X) (V : Set X) n τ hσ)
  · rw [relRetract_generator_of_not (V : Set X) n hV, map_zero]

theorem excisionCochainMap_surjective (R : Type) [CommRing R] (n : ℕ) :
    Function.Surjective ((excisionCochainMap U V R).f n).hom := by
  intro χ
  refine ⟨⟨_, excisionCochainMap_preimage U V R n χ⟩, ?_⟩
  refine Subtype.ext ?_
  have key : ∀ ψ : relCochainSubmodule R (TopCat.of (V : Set X))
      (excisedSub (U : Set X) (V : Set X)) n,
      singularChainMap R (sInclusion (V : Set X)) n
          ≫ (relRetract R X (V : Set X) n ≫ (ψ : singularCochainGroup R (TopCat.of (V : Set X)) n))
        = (ψ : singularCochainGroup R (TopCat.of (V : Set X)) n) := by
    intro ψ
    rw [← Category.assoc, singularChainMap_comp_relRetract, Category.id_comp]
  exact key χ

theorem ker_excisionCochainMap (R : Type) [CommRing R] (n : ℕ)
    (φ : relCochainSubmodule R X (U : Set X) n)
    (hφ : cochainPullback (sInclusion (V : Set X)) n
      (φ : singularCochainGroup R X n) = 0) :
    (φ : singularCochainGroup R X n) ∈ smallAnnSubmodule R X (twoSetCover U V hUV) n := by
  intro σ hσ
  rcases subordinate_or_of_isSmallSimplex U V hUV hσ with hU | hV
  · exact φ.2 σ hU
  · obtain ⟨τ, rfl⟩ := exists_pushSimplex_of_subordinate (V : Set X) n hV
    have h : cochainEval n
        (cochainPullback (sInclusion (V : Set X)) n
          (φ : singularCochainGroup R X n)) τ = 0 := by
      rw [hφ, cochainEval_zero]
    rw [cochainPullback_eval] at h
    exact h

theorem excisionShortComplex_degreewise_shortExact (R : Type) [CommRing R] (n : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapShortComplex.obj
      (excisionShortComplex U V hUV R)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    have hval := congrArg Subtype.val hx₂
    exact ⟨⟨_, ker_excisionCochainMap U V hUV R n x₂ hval⟩, Subtype.ext rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b hab
    have h2 := congrArg Subtype.val hab
    exact Subtype.ext h2
  · rw [ModuleCat.epi_iff_surjective]
    exact excisionCochainMap_surjective U V R n

/-- **The excision short exact sequence.** -/
theorem excisionShortExact (R : Type) [CommRing R] :
    (excisionShortComplex U V hUV R).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => excisionShortComplex_degreewise_shortExact U V hUV R n)

/-! ## 4. The excision isomorphism -/

/-- **Excision for an open cover.**  For opens `U, V` with `U ∪ V = X`, the inclusion
of pairs `(V, U ∩ V) → (X, U)` induces an isomorphism on mod-2 relative cohomology
in every degree. -/
theorem isIso_excision (hUV : U ⊔ V = ⊤) (n : ℕ) :
    IsIso (relPullback (ZMod 2) (sInclusion (V : Set X)) (excision_mapsTo U V) n) := by
  have hS := excisionShortExact U V hUV (ZMod 2)
  have h₁ : IsZero (((excisionShortComplex U V hUV (ZMod 2)).X₁).homology n) :=
    isZero_smallAnnComplex_homology X (twoSetCover U V hUV) n
  have h₂ : IsZero (((excisionShortComplex U V hUV (ZMod 2)).X₁).homology (n + 1)) :=
    isZero_smallAnnComplex_homology X (twoSetCover U V hUV) (n + 1)
  have hmono : Mono (HomologicalComplex.homologyMap
      (excisionShortComplex U V hUV (ZMod 2)).g n) :=
    (hS.homology_exact₂ n).mono_g (h₁.eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap
      (excisionShortComplex U V hUV (ZMod 2)).g n) :=
    (hS.homology_exact₃ n (n + 1) rfl).epi_f (h₂.eq_of_tgt _ _)
  show IsIso (HomologicalComplex.homologyMap (excisionShortComplex U V hUV (ZMod 2)).g n)
  exact isIso_of_mono_of_epi _

/-- The excision isomorphism `H^n(X, U; F₂) ≅ H^n(V, U ∩ V; F₂)`. -/
def excisionIso (hUV : U ⊔ V = ⊤) (n : ℕ) :
    relCohomology (ZMod 2) X (U : Set X) n ≅
      relCohomology (ZMod 2) (TopCat.of (V : Set X))
        (excisedSub (U : Set X) (V : Set X)) n :=
  haveI := isIso_excision U V hUV n
  asIso (relPullback (ZMod 2) (sInclusion (V : Set X)) (excision_mapsTo U V) n)

end

end GroupApproximation.CharClass
