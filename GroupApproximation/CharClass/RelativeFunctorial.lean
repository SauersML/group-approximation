import GroupApproximation.CharClass.RelativeLES

/-!
# Maps of pairs: functoriality, naturality of the long exact sequence

A **map of pairs** `f : (X, A) → (Y, B)` is a continuous map `f : X ⟶ Y` with
`f '' A ⊆ B`, recorded here as the hypothesis `∀ x ∈ A, f x ∈ B`.  Such an `f`
pulls relative cochains back to relative cochains (the pushforward of a simplex
with image in `A` has image in `B`), giving a cochain map
`relCochainMap` and hence `relPullback : H^n(Y, B) ⟶ H^n(X, A)`.

This file proves functoriality (`relCochainMap_id`, `relCochainMap_comp`), the
naturality of the whole long exact sequence of the pair, and, as a corollary,
that an isomorphism of pairs induces an isomorphism on relative cohomology
(`relPairIso`) — in particular a homeomorphism carrying `A` onto `B` does.

## Main definitions

* `restrictPairMap f hf : TopCat.of A ⟶ TopCat.of B` — the restriction of `f`.
* `relCochainMap R f hf : C^*(Y, B) ⟶ C^*(X, A)`.
* `relPullback R f hf n : H^n(Y, B) ⟶ H^n(X, A)`.
* `pairShortComplexMap R f hf` — the induced morphism of short exact sequences.
* `relPairIso` — the isomorphism induced by an isomorphism of pairs.

## Main results

* `relCochainMap_id`, `relCochainMap_comp`, `relPullback_id`, `relPullback_comp`.
* `relDelta_naturality`, `relToAbs_naturality`, `absToSub_naturality`.
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

variable {R : Type} [CommRing R] {X Y Z : TopCat.{0}}

/-! ## 1. Pullback of cochains, functorially -/

theorem cochainPullback_id (R : Type) [CommRing R] (W : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R W n) : cochainPullback (𝟙 W) n φ = φ := by
  show ((((singularCochainComplexFunctor R (ModuleCat.of R R)).map (𝟙 W).op).f n).hom) φ = φ
  rw [show (𝟙 W).op = 𝟙 (Opposite.op W) from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem cochainPullback_comp (R : Type) [CommRing R] (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (φ : singularCochainGroup R Z n) :
    cochainPullback (f ≫ g) n φ = cochainPullback f n (cochainPullback g n φ) := by
  show ((((singularCochainComplexFunctor R (ModuleCat.of R R)).map (f ≫ g).op).f n).hom) φ = _
  rw [show (f ≫ g).op = g.op ≫ f.op from rfl, Functor.map_comp]
  rfl

/-- The cochain pullback is a cochain map, over an arbitrary base ring. -/
theorem cochainPullback_cochainCoboundary' (R : Type) [CommRing R] (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup R Y n) :
    cochainCoboundary R X n (cochainPullback f n φ)
      = cochainPullback f (n + 1) (cochainCoboundary R Y n φ) := by
  have hcomm := ((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).comm n (n + 1)
  change ((cochainCx R X).d n (n + 1)).hom
      ((((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).f n).hom φ) = _
  rw [← ModuleCat.comp_apply, hcomm]
  rfl

/-! ## 2. Maps of pairs -/

/-- The pushforward of a simplex with image in `A` along a map of pairs has image
in `B`. -/
theorem isSubordinate_pushSimplex (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ) {σ : singularSimplices X n}
    (hσ : IsSubordinate A σ) : IsSubordinate B (pushSimplex f n σ) := by
  have hσ' : Set.range (singularSimplexAsContinuousMap X n σ) ⊆ A := hσ
  show Set.range (singularSimplexAsContinuousMap Y n (pushSimplex f n σ)) ⊆ B
  rw [pushSimplex_continuousMap f n σ, ContinuousMap.coe_comp, Set.range_comp]
  rintro _ ⟨x, hx, rfl⟩
  exact hf x (hσ' hx)

theorem cochainPullback_mem_relCochainSubmodule (R : Type) [CommRing R] (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ)
    (φ : singularCochainGroup R Y n) (hφ : φ ∈ relCochainSubmodule R Y B n) :
    cochainPullback f n φ ∈ relCochainSubmodule R X A n := by
  intro σ hσ
  rw [cochainPullback_eval]
  exact hφ _ (isSubordinate_pushSimplex f hf n hσ)

/-- The **cochain map of a map of pairs** `C^*(Y, B) ⟶ C^*(X, A)`. -/
def relCochainMap (R : Type) [CommRing R] (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) :
    relCochainComplex R Y B ⟶ relCochainComplex R X A where
  f n := ModuleCat.ofHom
    ((((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op).f n).hom.restrict
      (fun φ hφ => cochainPullback_mem_relCochainSubmodule R f hf n φ hφ))
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    rw [relCochainComplex_d, relCochainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    have key : ∀ ψ : relCochainSubmodule R Y B i,
        cochainCoboundary R X i (cochainPullback f i (ψ : singularCochainGroup R Y i))
          = cochainPullback f (i + 1)
            (cochainCoboundary R Y i (ψ : singularCochainGroup R Y i)) :=
      fun ψ => cochainPullback_cochainCoboundary' R f i _
    exact Subtype.ext (key φ)

theorem relCochainMap_f_val (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ)
    (φ : relCochainSubmodule R Y B n) :
    ((relCochainMap R f hf).f n).hom φ =
      ⟨cochainPullback f n (φ : singularCochainGroup R Y n),
        cochainPullback_mem_relCochainSubmodule R f hf n (φ : singularCochainGroup R Y n)
          φ.2⟩ := rfl

/-- The **pullback on relative cohomology** of a map of pairs. -/
def relPullback (R : Type) [CommRing R] (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ) :
    relCohomology R Y B n ⟶ relCohomology R X A n :=
  HomologicalComplex.homologyMap (relCochainMap R f hf) n

/-! ## 3. Functoriality -/

theorem relCochainMap_id (R : Type) [CommRing R] (W : TopCat.{0}) (A : Set W)
    (h : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 W)) x ∈ A) :
    relCochainMap R (𝟙 W) h = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have key : ∀ ψ : relCochainSubmodule R W A n,
      cochainPullback (𝟙 W) n (ψ : singularCochainGroup R W n)
        = (ψ : singularCochainGroup R W n) :=
    fun ψ => cochainPullback_id R W n _
  exact Subtype.ext (key φ)

theorem relCochainMap_comp (R : Type) [CommRing R] (f : X ⟶ Y) (g : Y ⟶ Z)
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ y ∈ B, (ConcreteCategory.hom g) y ∈ C)
    (hfg : ∀ x ∈ A, (ConcreteCategory.hom (f ≫ g)) x ∈ C) :
    relCochainMap R (f ≫ g) hfg = relCochainMap R g hg ≫ relCochainMap R f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have key : ∀ ψ : relCochainSubmodule R Z C n,
      cochainPullback (f ≫ g) n (ψ : singularCochainGroup R Z n)
        = cochainPullback f n (cochainPullback g n (ψ : singularCochainGroup R Z n)) :=
    fun ψ => cochainPullback_comp R f g n _
  exact Subtype.ext (key φ)

theorem relPullback_id (R : Type) [CommRing R] (W : TopCat.{0}) (A : Set W)
    (h : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 W)) x ∈ A) (n : ℕ) :
    relPullback R (𝟙 W) h n = 𝟙 _ := by
  rw [relPullback, relCochainMap_id, HomologicalComplex.homologyMap_id]

theorem relPullback_comp (R : Type) [CommRing R] (f : X ⟶ Y) (g : Y ⟶ Z)
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B)
    (hg : ∀ y ∈ B, (ConcreteCategory.hom g) y ∈ C)
    (hfg : ∀ x ∈ A, (ConcreteCategory.hom (f ≫ g)) x ∈ C) (n : ℕ) :
    relPullback R (f ≫ g) hfg n = relPullback R g hg n ≫ relPullback R f hf n := by
  rw [relPullback, relPullback, relPullback, relCochainMap_comp R f g hf hg hfg,
    HomologicalComplex.homologyMap_comp]

/-- `relPullback` only depends on the underlying morphism up to propositional
equality: transporting the map-of-pairs hypothesis along `f = g` gives the same
pullback.  Proved by `subst`, so that later rewriting the morphism (e.g. via an
isomorphism's `hom_inv_id`) never has to rewrite *through* the dependent
hypothesis argument. -/
theorem relPullback_eq_of_eq (R : Type) [CommRing R] {f g : X ⟶ Y} (hfg : f = g)
    {A : Set X} {B : Set Y} (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ) :
    relPullback R f hf n = relPullback R g (hfg ▸ hf) n := by
  subst hfg
  rfl

/-! ## 4. Isomorphisms of pairs -/

/-- An isomorphism of pairs induces an isomorphism on relative cohomology.  For a
homeomorphism carrying `A` onto `B`, apply this to `TopCat.isoOfHomeo`. -/
def relPairIso (R : Type) [CommRing R] (e : X ≅ Y) {A : Set X} {B : Set Y}
    (h₁ : ∀ x ∈ A, (ConcreteCategory.hom e.hom) x ∈ B)
    (h₂ : ∀ y ∈ B, (ConcreteCategory.hom e.inv) y ∈ A) (n : ℕ) :
    relCohomology R Y B n ≅ relCohomology R X A n where
  hom := relPullback R e.hom h₁ n
  inv := relPullback R e.inv h₂ n
  hom_inv_id := by
    have hp : ∀ x ∈ B, (ConcreteCategory.hom (e.inv ≫ e.hom)) x ∈ B := by
      intro x hx
      have hx' : (ConcreteCategory.hom (e.inv ≫ e.hom)) x = x := by
        rw [e.inv_hom_id, CategoryTheory.id_apply]
      rw [hx']; exact hx
    have step1 : relPullback R e.hom h₁ n ≫ relPullback R e.inv h₂ n
        = relPullback R (e.inv ≫ e.hom) hp n := (relPullback_comp R e.inv e.hom h₂ h₁ hp n).symm
    have step2 := relPullback_eq_of_eq R e.inv_hom_id hp n
    exact step1.trans (step2.trans (relPullback_id R Y _ _ n))
  inv_hom_id := by
    have hp : ∀ x ∈ A, (ConcreteCategory.hom (e.hom ≫ e.inv)) x ∈ A := by
      intro x hx
      have hx' : (ConcreteCategory.hom (e.hom ≫ e.inv)) x = x := by
        rw [e.hom_inv_id, CategoryTheory.id_apply]
      rw [hx']; exact hx
    have step1 : relPullback R e.inv h₂ n ≫ relPullback R e.hom h₁ n
        = relPullback R (e.hom ≫ e.inv) hp n := (relPullback_comp R e.hom e.inv h₁ h₂ hp n).symm
    have step2 := relPullback_eq_of_eq R e.hom_inv_id hp n
    exact step1.trans (step2.trans (relPullback_id R X _ _ n))

/-! ## 5. Naturality of the long exact sequence -/

/-- The restriction of a map of pairs to the subspaces. -/
def restrictPairMap (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom
    { toFun := fun a => ⟨(ConcreteCategory.hom f) a.1, hf a.1 a.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (ConcreteCategory.hom f).continuous.comp continuous_subtype_val }

theorem sInclusion_comp_map (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) :
    sInclusion A ≫ f = restrictPairMap f hf ≫ sInclusion B := rfl

/-- The morphism of short exact sequences of cochain complexes induced by a map of
pairs. -/
def pairShortComplexMap (R : Type) [CommRing R] (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) :
    pairShortComplex R Y B ⟶ pairShortComplex R X A where
  τ₁ := relCochainMap R f hf
  τ₂ := (singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op
  τ₃ := (singularCochainComplexFunctor R (ModuleCat.of R R)).map (restrictPairMap f hf).op
  comm₁₂ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl
  comm₂₃ := by
    show (singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op
        ≫ (singularCochainComplexFunctor R (ModuleCat.of R R)).map (sInclusion A).op
      = (singularCochainComplexFunctor R (ModuleCat.of R R)).map (sInclusion B).op
        ≫ (singularCochainComplexFunctor R (ModuleCat.of R R)).map (restrictPairMap f hf).op
    rw [← Functor.map_comp, ← Functor.map_comp,
      show f.op ≫ (sInclusion A).op = (sInclusion A ≫ f).op from rfl,
      show (sInclusion B).op ≫ (restrictPairMap f hf).op
        = (restrictPairMap f hf ≫ sInclusion B).op from rfl,
      sInclusion_comp_map f hf]

/-- **Naturality of `j^*`.** -/
theorem relToAbs_naturality (R : Type) [CommRing R] (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ) :
    relToAbs R Y B n ≫ HomologicalComplex.homologyMap
        ((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op) n
      = relPullback R f hf n ≫ relToAbs R X A n := by
  rw [relToAbs, relToAbs, relPullback, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun t => HomologicalComplex.homologyMap t n)
    (pairShortComplexMap R f hf).comm₁₂.symm

/-- **Naturality of `i^*`.** -/
theorem absToSub_naturality (R : Type) [CommRing R] (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ) :
    absToSub R B n ≫ HomologicalComplex.homologyMap
        ((singularCochainComplexFunctor R (ModuleCat.of R R)).map (restrictPairMap f hf).op) n
      = HomologicalComplex.homologyMap
          ((singularCochainComplexFunctor R (ModuleCat.of R R)).map f.op) n ≫ absToSub R A n := by
  rw [absToSub, absToSub, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun t => HomologicalComplex.homologyMap t n)
    (pairShortComplexMap R f hf).comm₂₃.symm

/-- **Naturality of the connecting map `δ`.** -/
theorem relDelta_naturality (R : Type) [CommRing R] (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ B) (n : ℕ) :
    relDelta R Y B n ≫ relPullback R f hf (n + 1)
      = HomologicalComplex.homologyMap
          ((singularCochainComplexFunctor R (ModuleCat.of R R)).map
            (restrictPairMap f hf).op) n ≫ relDelta R X A n :=
  HomologicalComplex.HomologySequence.δ_naturality (pairShortComplexMap R f hf)
    (pairShortExact R Y B) (pairShortExact R X A) n (n + 1) rfl

end

end GroupApproximation.CharClass
