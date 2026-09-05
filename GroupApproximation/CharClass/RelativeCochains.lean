import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct

/-!
# Relative singular cochains and relative cohomology

For a space `X : TopCat.{0}` and a subset `A ⊆ X`, the **relative cochain group**
`C^n(X, A; R)` is the submodule of `C^n(X; R)` of cochains vanishing on every
singular simplex whose image lies in `A` (`relCochainSubmodule`).  The singular
coboundary preserves this submodule (a face of a simplex with image in `A` again
has image in `A`), so the relative cochains form a cochain complex
`relCochainComplex R X A`, whose `n`-th homology is the **relative cohomology**
`relCohomology R X A n = H^n(X, A; R)`.

The point of the construction is the short exact sequence of cochain complexes

```text
0 → C^*(X, A) → C^*(X) → C^*(A) → 0
```

(`pairShortComplex`, `pairShortExact`), whose third term is the cochain complex of
the *subspace* `A` and whose surjectivity comes from a retraction of singular
chains: the singular chains of `X` supported in `A` are spanned by a subset of a
basis, so they split off (`subKeep`), and they are the singular chains of the
subspace `A` (the vendored isomorphism `subChainCorestrict`).  Mathlib's homology
long exact sequence of a short exact sequence of complexes then gives the long
exact sequence of the pair; see `RelativeLES.lean`.

## Main definitions

* `cochainCx R X` — the singular cochain complex of `X` with coefficients in `R`
  (the object of the vendored `singularCochainComplexFunctor`).
* `relCochainSubmodule R X A n` — the relative cochains `C^n(X, A; R)`.
* `relCochainComplex R X A` — the relative cochain complex.
* `relCohomology R X A n` — `H^n(X, A; R)`.
* `relInclusion R X A` — the cochain map `C^*(X, A) ⟶ C^*(X)`.
* `pairRestriction R A` — the cochain map `C^*(X) ⟶ C^*(A)`.
* `pairShortComplex R X A`, `pairShortExact R X A` — the short exact sequence of
  the pair.

## Main results

* `pairShortComplex_degreewise_shortExact` — degreewise short exactness.
* `pairShortExact` — short exactness as a sequence of cochain complexes.
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

open Classical

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 0. The absolute cochain complex -/

/-- The singular cochain complex `C^*(X; R)` (coefficients in `R` itself).  This is
the object of the vendored `singularCochainComplexFunctor`; for `R = ZMod 2` it is
`cochainCxZMod2 X`. -/
abbrev cochainCx (R : Type) [CommRing R] (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (singularCochainComplexFunctor R (ModuleCat.of R R)).obj (Opposite.op X)

/-- The differential of `cochainCx` is the cochain coboundary. -/
theorem cochainCx_d_apply (R : Type) [CommRing R] (Z : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R Z n) :
    ((cochainCx R Z).d n (n + 1)).hom φ = cochainCoboundary R Z n φ := rfl

/-- `δ ∘ δ = 0` for the singular cochain coboundary, over an arbitrary base ring. -/
theorem cochainCoboundary_cochainCoboundary' (R : Type) [CommRing R] (Z : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup R Z m) :
    cochainCoboundary R Z (m + 1) (cochainCoboundary R Z m η) = 0 := by
  change ((cochainCx R Z).d m (m + 1) ≫ (cochainCx R Z).d (m + 1) (m + 2)).hom η = 0
  rw [(cochainCx R Z).d_comp_d]
  rfl

/-! ## 1. The relative cochain submodule -/

/-- The **relative cochains** `C^n(X, A; R)`: the singular `n`-cochains of `X`
vanishing on every singular simplex whose image lies in `A`. -/
def relCochainSubmodule (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Submodule R (singularCochainGroup R X n) where
  carrier := {φ | ∀ σ : singularSimplices X n, IsSubordinate A σ → cochainEval n φ σ = 0}
  add_mem' := fun {a b} ha hb σ hσ => by
    rw [cochainEval_add, ha σ hσ, hb σ hσ, add_zero]
  zero_mem' := fun σ _ => cochainEval_zero n σ
  smul_mem' := fun c a ha σ hσ => by
    rw [cochainEval_smul, ha σ hσ, mul_zero]

theorem mem_relCochainSubmodule {A : Set X} {n : ℕ} {φ : singularCochainGroup R X n} :
    φ ∈ relCochainSubmodule R X A n ↔
      ∀ σ : singularSimplices X n, IsSubordinate A σ → cochainEval n φ σ = 0 :=
  Iff.rfl

/-- The coboundary of a relative cochain is a relative cochain: every face of a
simplex with image in `A` again has image in `A`. -/
theorem cochainCoboundary_mem_relCochainSubmodule (R : Type) [CommRing R] {X : TopCat.{0}}
    (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n)
    (hφ : φ ∈ relCochainSubmodule R X A n) :
    cochainCoboundary R X n φ ∈ relCochainSubmodule R X A (n + 1) := by
  intro σ hσ
  rw [cochainCoboundary_eval]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [hφ _ (hσ.face i), mul_zero]

/-- The relative coboundary `δ : C^n(X, A) ⟶ C^{n+1}(X, A)`. -/
def relD (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.of R (relCochainSubmodule R X A n) ⟶
      ModuleCat.of R (relCochainSubmodule R X A (n + 1)) :=
  ModuleCat.ofHom
    (((cochainCx R X).d n (n + 1)).hom.restrict
      (fun φ hφ => cochainCoboundary_mem_relCochainSubmodule R A n φ hφ))

@[simp] theorem relD_val (A : Set X) (n : ℕ) (φ : relCochainSubmodule R X A n) :
    (((relD R X A n).hom φ : relCochainSubmodule R X A (n + 1)) :
        singularCochainGroup R X (n + 1))
      = cochainCoboundary R X n (φ : singularCochainGroup R X n) := rfl

theorem relD_comp_relD (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relD R X A n ≫ relD R X A (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  show cochainCoboundary R X (n + 1)
      (cochainCoboundary R X n (φ : singularCochainGroup R X n)) = 0
  exact cochainCoboundary_cochainCoboundary' R X n _

/-! ## 2. The relative cochain complex and relative cohomology -/

/-- The **relative cochain complex** `C^*(X, A; R)`. -/
def relCochainComplex (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (relCochainSubmodule R X A n))
    (fun n => relD R X A n) (fun n => relD_comp_relD R X A n)

@[simp] theorem relCochainComplex_X (A : Set X) (n : ℕ) :
    (relCochainComplex R X A).X n = ModuleCat.of R (relCochainSubmodule R X A n) := rfl

@[simp] theorem relCochainComplex_d (A : Set X) (n : ℕ) :
    (relCochainComplex R X A).d n (n + 1) = relD R X A n := by
  unfold relCochainComplex
  exact CochainComplex.of_d (fun k => ModuleCat.of R (relCochainSubmodule R X A k))
    (fun k => relD R X A k) n

/-- The **relative cohomology** `H^n(X, A; R)`. -/
abbrev relCohomology (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.{0} R :=
  (relCochainComplex R X A).homology n

/-! ## 3. The two cochain maps of the pair -/

/-- The inclusion `C^*(X, A) ⟶ C^*(X)` of relative cochains into cochains. -/
def relInclusion (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    relCochainComplex R X A ⟶ cochainCx R X where
  f n := ModuleCat.ofHom (relCochainSubmodule R X A n).subtype
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    rw [relCochainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

@[simp] theorem relInclusion_f_apply (A : Set X) (n : ℕ) (φ : relCochainSubmodule R X A n) :
    ((relInclusion R X A).f n).hom φ = (φ : singularCochainGroup R X n) := rfl

/-- The restriction `C^*(X) ⟶ C^*(A)` of cochains to the subspace `A`. -/
def pairRestriction (R : Type) [CommRing R] {X : TopCat.{0}} (A : Set X) :
    cochainCx R X ⟶ cochainCx R (TopCat.of A) :=
  (singularCochainComplexFunctor R (ModuleCat.of R R)).map (sInclusion A).op

@[simp] theorem pairRestriction_f_apply (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n) :
    ((pairRestriction R A).f n).hom φ = cochainPullback (sInclusion A) n φ := rfl

theorem relInclusion_comp_pairRestriction (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    relInclusion R X A ≫ pairRestriction R A = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  show cochainPullback (sInclusion A) n (φ : singularCochainGroup R X n) = 0
  apply cochain_ext
  intro τ
  rw [cochainPullback_eval, cochainEval_zero]
  exact φ.2 _ (isSubordinate_pushSimplex_sInclusion A n τ)

/-! ## 4. The chain-level retraction of `A`-supported chains -/

/-- The degree-`n` component of the projection of singular chains onto the chains
supported in `S`, at a fixed simplex. -/
def subKeepComp (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X) (n : ℕ)
    (σ : singularSimplices X n) :
    ModuleCat.of R R ⟶ ModuleCat.of R (subChainSubmodule R X S n) :=
  if h : IsSubordinate S σ then
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _
      (⟨chainGenerator R X n σ, chainGenerator_mem_subChainSubmodule h⟩ :
        subChainSubmodule R X S n))
  else 0

/-- The **coordinate projection onto chains supported in `S`**: it keeps the basis
chains of simplices with image in `S` and kills the rest.  Well defined because
the singular chain group is free on the singular simplices. -/
def subKeep (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X) (n : ℕ) :
    singularChainGroup R X n ⟶ ModuleCat.of R (subChainSubmodule R X S n) :=
  Sigma.desc (subKeepComp R X S n)

theorem subKeep_generator (S : Set X) (n : ℕ) {σ : singularSimplices X n}
    (hσ : IsSubordinate S σ) :
    (((subKeep R X S n).hom (chainGenerator R X n σ) : subChainSubmodule R X S n) :
        singularChainGroup R X n) = chainGenerator R X n σ := by
  have h : Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ ≫ subKeep R X S n
      = subKeepComp R X S n σ := Sigma.ι_desc _ _
  have h2 := congrArg
    (fun f : ModuleCat.of R R ⟶ ModuleCat.of R (subChainSubmodule R X S n) => f.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : subKeepComp R X S n σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R _
        (⟨chainGenerator R X n σ, chainGenerator_mem_subChainSubmodule hσ⟩ :
          subChainSubmodule R X S n)) := by
    unfold subKeepComp
    rw [dif_pos hσ]
  rw [h3] at h2
  have h4 : ((subKeep R X S n).hom (chainGenerator R X n σ) : subChainSubmodule R X S n)
      = ⟨chainGenerator R X n σ, chainGenerator_mem_subChainSubmodule hσ⟩ := by
    refine h2.trans ?_
    show (1 : R) • (⟨chainGenerator R X n σ, chainGenerator_mem_subChainSubmodule hσ⟩ :
      subChainSubmodule R X S n) = _
    rw [one_smul]
  rw [h4]

/-- The projection restricts to the identity on the chains supported in `S`. -/
theorem subtype_comp_subKeep (S : Set X) (n : ℕ) :
    ModuleCat.ofHom (subChainSubmodule R X S n).subtype ≫ subKeep R X S n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨c, hc⟩
  apply Subtype.ext
  show (((subKeep R X S n).hom c : subChainSubmodule R X S n) :
      singularChainGroup R X n) = c
  refine subChainSubmodule_induction (S := S)
    (p := fun x => (((subKeep R X S n).hom x : subChainSubmodule R X S n) :
      singularChainGroup R X n) = x) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    exact subKeep_generator S n hσ
  · show (((subKeep R X S n).hom 0 : subChainSubmodule R X S n) :
      singularChainGroup R X n) = 0
    rw [map_zero]
    rfl
  · intro x y hx hy
    show (((subKeep R X S n).hom (x + y) : subChainSubmodule R X S n) :
      singularChainGroup R X n) = x + y
    rw [map_add]
    change ((subKeep R X S n).hom x : subChainSubmodule R X S n).1
      + ((subKeep R X S n).hom y : subChainSubmodule R X S n).1 = x + y
    rw [hx, hy]
  · intro a x hx
    show (((subKeep R X S n).hom (a • x) : subChainSubmodule R X S n) :
      singularChainGroup R X n) = a • x
    rw [map_smul]
    change a • ((subKeep R X S n).hom x : subChainSubmodule R X S n).1 = a • x
    rw [hx]

/-- The chain map induced by the inclusion of the subspace `A`, factored through the
chains supported in `A`. -/
theorem singularChainMap_sInclusion_eq (A : Set X) (n : ℕ) :
    singularChainMap R (sInclusion A) n
      = (subChainCorestrict R X A).f n
          ≫ ModuleCat.ofHom (subChainSubmodule R X A n).subtype := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- A retraction of the chain map induced by the inclusion `A ↪ X`. -/
def relRetract (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    singularChainGroup R X n ⟶ singularChainGroup R (TopCat.of A) n :=
  subKeep R X A n ≫ inv ((subChainCorestrict R X A).f n)

theorem singularChainMap_comp_relRetract (A : Set X) (n : ℕ) :
    singularChainMap R (sInclusion A) n ≫ relRetract R X A n = 𝟙 _ := by
  rw [relRetract, singularChainMap_sInclusion_eq, Category.assoc,
    ← Category.assoc (ModuleCat.ofHom (subChainSubmodule R X A n).subtype),
    subtype_comp_subKeep, Category.id_comp, IsIso.hom_inv_id]

/-! ## 5. The short exact sequence of the pair -/

/-- The short complex `C^*(X, A) → C^*(X) → C^*(A)`. -/
def pairShortComplex (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk (relInclusion R X A) (pairRestriction R A)
    (relInclusion_comp_pairRestriction R X A)

theorem pairRestriction_surjective (A : Set X) (n : ℕ) :
    Function.Surjective ((pairRestriction R A).f n).hom := by
  intro ψ
  refine ⟨relRetract R X A n ≫ ψ, ?_⟩
  show cochainPullback (sInclusion A) n (relRetract R X A n ≫ ψ) = ψ
  show singularChainMap R (sInclusion A) n ≫ (relRetract R X A n ≫ ψ) = ψ
  rw [← Category.assoc, singularChainMap_comp_relRetract, Category.id_comp]

theorem ker_pairRestriction (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n)
    (hφ : ((pairRestriction R A).f n).hom φ = 0) : φ ∈ relCochainSubmodule R X A n := by
  intro σ hσ
  obtain ⟨τ, rfl⟩ := exists_pushSimplex_of_subordinate A n hσ
  have h : cochainEval n (cochainPullback (sInclusion A) n φ) τ = 0 := by
    rw [show cochainPullback (sInclusion A) n φ = 0 from hφ, cochainEval_zero]
  rw [cochainPullback_eval] at h
  exact h

theorem pairShortComplex_degreewise_shortExact (R : Type) [CommRing R] (X : TopCat.{0})
    (A : Set X) (n : ℕ) :
    ((HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapShortComplex.obj
      (pairShortComplex R X A)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact ⟨⟨x₂, ker_pairRestriction A n x₂ hx₂⟩, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact fun a b hab => Subtype.ext hab
  · rw [ModuleCat.epi_iff_surjective]
    exact pairRestriction_surjective A n

/-- **The short exact sequence of the pair `(X, A)`**:
`0 → C^*(X, A) → C^*(X) → C^*(A) → 0`. -/
theorem pairShortExact (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    (pairShortComplex R X A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => pairShortComplex_degreewise_shortExact R X A n)

end

end GroupApproximation.CharClass
