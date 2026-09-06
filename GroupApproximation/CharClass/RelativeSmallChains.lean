import GroupApproximation.CharClass.RelativeDual

/-!
# Cochains vanishing on small chains form an acyclic complex

Fix an open cover `𝒰` of `X`.  The cochains of `X` that vanish on every
`𝒰`-small simplex form a subcomplex `smallAnnComplex` of `C^*(X; F₂)`, and it sits
in a short exact sequence

```text
0 → smallAnnComplex → C^*(X) → Hom(C_*^𝒰(X), F₂) → 0
```

whose third map is the dual of the small-chain inclusion.  The vendored
small-simplices theorem says that inclusion is a quasi-isomorphism, and
`RelativeDual.lean` says its dual is one too; therefore the kernel
`smallAnnComplex` is **acyclic**.  This is the whole geometric input of excision:
everything else is bookkeeping with coordinate projections on the free singular
chain groups.

## Main results

* `smallAnnComplex_shortExact` — the displayed short exact sequence.
* `isZero_smallAnnComplex_homology` — `H^n` of the small-annihilator complex vanishes.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

open Classical

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. The coordinate projection onto small chains -/

/-- Component of the coordinate projection onto the `𝒰`-small chains. -/
def smallKeepComp (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ)
    (σ : singularSimplices X n) :
    ModuleCat.of R R ⟶ ModuleCat.of R (smallChainSubmodule R X 𝒰 n) :=
  if h : IsSmallSimplex 𝒰 σ then
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _
      (⟨chainGenerator R X n σ, chainGenerator_mem_smallChainSubmodule h⟩ :
        smallChainSubmodule R X 𝒰 n))
  else 0

/-- The coordinate projection of singular chains onto the `𝒰`-small chains. -/
def smallKeep (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    singularChainGroup R X n ⟶ ModuleCat.of R (smallChainSubmodule R X 𝒰 n) :=
  Sigma.desc (smallKeepComp R X 𝒰 n)

theorem smallKeep_generator (𝒰 : OpenCoverData X) (n : ℕ) {σ : singularSimplices X n}
    (hσ : IsSmallSimplex 𝒰 σ) :
    (((smallKeep R X 𝒰 n).hom (chainGenerator R X n σ) : smallChainSubmodule R X 𝒰 n) :
        singularChainGroup R X n) = chainGenerator R X n σ := by
  have h : Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ
      ≫ smallKeep R X 𝒰 n = smallKeepComp R X 𝒰 n σ := Sigma.ι_desc _ _
  have h2 := congrArg
    (fun f : ModuleCat.of R R ⟶ ModuleCat.of R (smallChainSubmodule R X 𝒰 n) =>
      f.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : smallKeepComp R X 𝒰 n σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R _
        (⟨chainGenerator R X n σ, chainGenerator_mem_smallChainSubmodule hσ⟩ :
          smallChainSubmodule R X 𝒰 n)) := by
    unfold smallKeepComp
    rw [dif_pos hσ]
  rw [h3] at h2
  have h4 : ((smallKeep R X 𝒰 n).hom (chainGenerator R X n σ) :
      smallChainSubmodule R X 𝒰 n)
      = ⟨chainGenerator R X n σ, chainGenerator_mem_smallChainSubmodule hσ⟩ := by
    refine h2.trans ?_
    show (1 : R) • (⟨chainGenerator R X n σ, chainGenerator_mem_smallChainSubmodule hσ⟩ :
      smallChainSubmodule R X 𝒰 n) = _
    rw [one_smul]
  rw [h4]

theorem subtype_comp_smallKeep (𝒰 : OpenCoverData X) (n : ℕ) :
    ModuleCat.ofHom (smallChainSubmodule R X 𝒰 n).subtype ≫ smallKeep R X 𝒰 n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨c, hc⟩
  apply Subtype.ext
  show (((smallKeep R X 𝒰 n).hom c : smallChainSubmodule R X 𝒰 n) :
      singularChainGroup R X n) = c
  refine smallChainSubmodule_induction (𝒰 := 𝒰)
    (p := fun x => (((smallKeep R X 𝒰 n).hom x : smallChainSubmodule R X 𝒰 n) :
      singularChainGroup R X n) = x) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    exact smallKeep_generator 𝒰 n hσ
  · show (((smallKeep R X 𝒰 n).hom 0 : smallChainSubmodule R X 𝒰 n) :
      singularChainGroup R X n) = 0
    rw [map_zero]
    rfl
  · intro x y hx hy
    show (((smallKeep R X 𝒰 n).hom (x + y) : smallChainSubmodule R X 𝒰 n) :
      singularChainGroup R X n) = x + y
    rw [map_add]
    change ((smallKeep R X 𝒰 n).hom x : smallChainSubmodule R X 𝒰 n).1
      + ((smallKeep R X 𝒰 n).hom y : smallChainSubmodule R X 𝒰 n).1 = x + y
    rw [hx, hy]
  · intro a x hx
    show (((smallKeep R X 𝒰 n).hom (a • x) : smallChainSubmodule R X 𝒰 n) :
      singularChainGroup R X n) = a • x
    rw [map_smul]
    change a • ((smallKeep R X 𝒰 n).hom x : smallChainSubmodule R X 𝒰 n).1 = a • x
    rw [hx]

/-! ## 2. The complex of cochains vanishing on small chains -/

/-- The cochains vanishing on every `𝒰`-small simplex. -/
def smallAnnSubmodule (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    Submodule R (singularCochainGroup R X n) where
  carrier := {φ | ∀ σ : singularSimplices X n, IsSmallSimplex 𝒰 σ → cochainEval n φ σ = 0}
  add_mem' := fun {a b} ha hb σ hσ => by
    rw [cochainEval_add, ha σ hσ, hb σ hσ, add_zero]
  zero_mem' := fun σ _ => cochainEval_zero n σ
  smul_mem' := fun c a ha σ hσ => by
    rw [cochainEval_smul, ha σ hσ, mul_zero]

theorem cochainCoboundary_mem_smallAnnSubmodule (R : Type) [CommRing R] {X : TopCat.{0}}
    (𝒰 : OpenCoverData X) (n : ℕ) (φ : singularCochainGroup R X n)
    (hφ : φ ∈ smallAnnSubmodule R X 𝒰 n) :
    cochainCoboundary R X n φ ∈ smallAnnSubmodule R X 𝒰 (n + 1) := by
  intro σ hσ
  rw [cochainCoboundary_eval]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [hφ _ (hσ.face i), mul_zero]

/-- The coboundary on the small-annihilator cochains. -/
def smallAnnD (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    ModuleCat.of R (smallAnnSubmodule R X 𝒰 n) ⟶
      ModuleCat.of R (smallAnnSubmodule R X 𝒰 (n + 1)) :=
  ModuleCat.ofHom
    (((cochainCx R X).d n (n + 1)).hom.restrict
      (fun φ hφ => cochainCoboundary_mem_smallAnnSubmodule R 𝒰 n φ hφ))

theorem smallAnnD_comp_smallAnnD (R : Type) [CommRing R] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) (n : ℕ) :
    smallAnnD R X 𝒰 n ≫ smallAnnD R X 𝒰 (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  show cochainCoboundary R X (n + 1)
      (cochainCoboundary R X n (φ : singularCochainGroup R X n)) = 0
  exact cochainCoboundary_cochainCoboundary' R X n _

/-- The complex of cochains vanishing on all `𝒰`-small chains. -/
def smallAnnComplex (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (smallAnnSubmodule R X 𝒰 n))
    (fun n => smallAnnD R X 𝒰 n) (fun n => smallAnnD_comp_smallAnnD R X 𝒰 n)

@[simp] theorem smallAnnComplex_d (𝒰 : OpenCoverData X) (n : ℕ) :
    (smallAnnComplex R X 𝒰).d n (n + 1) = smallAnnD R X 𝒰 n := by
  unfold smallAnnComplex
  exact CochainComplex.of_d (fun k => ModuleCat.of R (smallAnnSubmodule R X 𝒰 k))
    (fun k => smallAnnD R X 𝒰 k) n

/-- The inclusion of the small-annihilator cochains into all cochains. -/
def smallAnnInclusion (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) :
    smallAnnComplex R X 𝒰 ⟶ cochainCx R X where
  f n := ModuleCat.ofHom (smallAnnSubmodule R X 𝒰 n).subtype
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    rw [smallAnnComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

/-- Restriction of cochains to small chains: the dual of the small-chain inclusion. -/
def smallRestriction (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) :
    cochainCx R X ⟶ dualCx R (smallChainComplex R X 𝒰) :=
  dualMap R (smallChainsInclusion R X 𝒰)

theorem smallRestriction_f_apply (𝒰 : OpenCoverData X) (n : ℕ)
    (φ : singularCochainGroup R X n) :
    ((smallRestriction R X 𝒰).f n).hom φ
      = ModuleCat.ofHom (smallChainSubmodule R X 𝒰 n).subtype ≫ φ := rfl

theorem smallAnn_comp (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) :
    smallAnnInclusion R X 𝒰 ≫ smallRestriction R X 𝒰 = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have key : ∀ ψ : smallAnnSubmodule R X 𝒰 n,
      ModuleCat.ofHom (smallChainSubmodule R X 𝒰 n).subtype
        ≫ (ψ : singularCochainGroup R X n) = 0 := by
   intro ψ
   apply ModuleCat.hom_ext
   apply LinearMap.ext
   rintro ⟨c, hc⟩
   show (ψ : singularCochainGroup R X n).hom c = 0
   refine smallChainSubmodule_induction (𝒰 := 𝒰)
    (p := fun x => (ψ : singularCochainGroup R X n).hom x = 0) ?_ ?_ ?_ ?_ hc
   · intro σ hσ
     exact ψ.2 σ hσ
   · exact map_zero _
   · intro x y hx hy
     rw [map_add, hx, hy, add_zero]
   · intro a x hx
     rw [map_smul, hx, smul_zero]
  exact key φ

/-- The short complex `smallAnn → C^*(X) → Hom(C_*^𝒰(X), R)`. -/
def smallAnnShortComplex (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk (smallAnnInclusion R X 𝒰) (smallRestriction R X 𝒰) (smallAnn_comp R X 𝒰)

theorem smallRestriction_surjective (𝒰 : OpenCoverData X) (n : ℕ) :
    Function.Surjective ((smallRestriction R X 𝒰).f n).hom := by
  intro ψ
  refine ⟨smallKeep R X 𝒰 n ≫ ψ, ?_⟩
  show ModuleCat.ofHom (smallChainSubmodule R X 𝒰 n).subtype ≫ (smallKeep R X 𝒰 n ≫ ψ) = ψ
  rw [← Category.assoc, subtype_comp_smallKeep, Category.id_comp]

theorem ker_smallRestriction (𝒰 : OpenCoverData X) (n : ℕ)
    (φ : singularCochainGroup R X n)
    (hφ : ((smallRestriction R X 𝒰).f n).hom φ = 0) : φ ∈ smallAnnSubmodule R X 𝒰 n := by
  intro σ hσ
  have hφ' : ModuleCat.ofHom (smallChainSubmodule R X 𝒰 n).subtype ≫ φ = 0 := hφ
  have h := congrArg
    (fun (g : ModuleCat.of R (smallChainSubmodule R X 𝒰 n) ⟶ ModuleCat.of R R) =>
      g.hom ⟨chainGenerator R X n σ, chainGenerator_mem_smallChainSubmodule hσ⟩) hφ'
  show φ.hom (chainGenerator R X n σ) = 0
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h

theorem smallAnnShortComplex_degreewise_shortExact (R : Type) [CommRing R] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) (n : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapShortComplex.obj
      (smallAnnShortComplex R X 𝒰)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact ⟨⟨x₂, ker_smallRestriction 𝒰 n x₂ hx₂⟩, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact fun a b hab => Subtype.ext hab
  · rw [ModuleCat.epi_iff_surjective]
    exact smallRestriction_surjective 𝒰 n

theorem smallAnnShortComplex_shortExact (R : Type) [CommRing R] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) : (smallAnnShortComplex R X 𝒰).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => smallAnnShortComplex_degreewise_shortExact R X 𝒰 n)

/-! ## 3. Acyclicity -/

/-- **The small-annihilator complex is acyclic.**  This is the small-simplices
theorem, dualized: restricting a cochain to small chains is a quasi-isomorphism, so
its kernel has vanishing cohomology. -/
theorem smallAnnComplex_acyclic (X : TopCat.{0}) (𝒰 : OpenCoverData X) :
    (smallAnnComplex (ZMod 2) X 𝒰).Acyclic :=
  (smallAnnShortComplex_shortExact (ZMod 2) X 𝒰).acyclic_X₁
    (inferInstanceAs (QuasiIso (dualMap (ZMod 2) (smallChainsInclusion (ZMod 2) X 𝒰))))

theorem isZero_smallAnnComplex_homology (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    IsZero ((smallAnnComplex (ZMod 2) X 𝒰).homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (smallAnnComplex_acyclic X 𝒰 n)

end

end GroupApproximation.CharClass
