import GroupApproximation.CharClass.RelativeCochains

/-!
# The long exact sequence of a pair

From the short exact sequence of cochain complexes `0 → C^*(X, A) → C^*(X) → C^*(A) → 0`
(`pairShortExact`) and Mathlib's homology long exact sequence of a short exact
sequence of complexes, this file packages the **long exact sequence of the pair
`(X, A)`**

```text
⋯ → H^n(X, A) →(j^*) H^n(X) →(i^*) H^n(A) →(δ) H^{n+1}(X, A) → ⋯
```

with the three maps `relToAbs`, `absToSub`, `relDelta`, exactness at each spot
stated in element form, and the two standard corollaries: the connecting map is an
isomorphism when the absolute cohomology vanishes in two consecutive degrees
(`relDeltaIso`), and `j^*` is an isomorphism when the cohomology of the subspace
vanishes in two consecutive degrees (`isIso_relToAbs`).

The degenerate case `A = ∅` is also settled: no singular simplex has image in `∅`,
so the relative cochains are all cochains and `H^n(X, ∅) ≅ H^n(X)`
(`relEmptyIso`).
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. The three maps -/

/-- `j^* : H^n(X, A) ⟶ H^n(X)`, induced by the inclusion of relative cochains. -/
def relToAbs (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relCohomology R X A n ⟶ (cochainCx R X).homology n :=
  HomologicalComplex.homologyMap (relInclusion R X A) n

/-- `i^* : H^n(X) ⟶ H^n(A)`, the pullback along the inclusion of the subspace. -/
def absToSub (R : Type) [CommRing R] {X : TopCat.{0}} (A : Set X) (n : ℕ) :
    (cochainCx R X).homology n ⟶ (cochainCx R (TopCat.of A)).homology n :=
  HomologicalComplex.homologyMap (pairRestriction R A) n

/-- `i^*` is the cohomology pullback of the inclusion of the subspace. -/
theorem absToSub_eq_cohPullback (A : Set X) (n : ℕ) :
    absToSub (ZMod 2) A n = cohPullback (sInclusion A) n := rfl

/-- The **connecting map** `δ : H^n(A) ⟶ H^{n+1}(X, A)` of the pair. -/
def relDelta (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (cochainCx R (TopCat.of A)).homology n ⟶ relCohomology R X A (n + 1) :=
  (pairShortExact R X A).δ n (n + 1) rfl

/-! ## 2. The composites vanish -/

theorem relToAbs_comp_absToSub (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relToAbs R X A n ≫ absToSub R A n = 0 := by
  rw [relToAbs, absToSub, ← HomologicalComplex.homologyMap_comp,
    relInclusion_comp_pairRestriction, HomologicalComplex.homologyMap_zero]

theorem absToSub_comp_relDelta (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    absToSub R A n ≫ relDelta R X A n = 0 :=
  (pairShortExact R X A).comp_δ n (n + 1) rfl

theorem relDelta_comp_relToAbs (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relDelta R X A n ≫ relToAbs R X A (n + 1) = 0 :=
  (pairShortExact R X A).δ_comp n (n + 1) rfl

/-! ## 3. Exactness, in element form -/

/-- **Exactness at `H^n(X)`.** A class of `X` restricting to zero on `A` comes from
a relative class. -/
theorem relLES_exact_abs (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : (cochainCx R X).homology n) (ha : (absToSub R A n).hom a = 0) :
    ∃ b : relCohomology R X A n, (relToAbs R X A n).hom b = a :=
  (ShortComplex.moduleCat_exact_iff _).1 ((pairShortExact R X A).homology_exact₂ n) a ha

/-- **Exactness at `H^n(A)`.** A class of `A` killed by the connecting map is a
restriction. -/
theorem relLES_exact_sub (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : (cochainCx R (TopCat.of A)).homology n) (ha : (relDelta R X A n).hom a = 0) :
    ∃ b : (cochainCx R X).homology n, (absToSub R A n).hom b = a :=
  (ShortComplex.moduleCat_exact_iff _).1
    ((pairShortExact R X A).homology_exact₃ n (n + 1) rfl) a ha

/-- **Exactness at `H^{n+1}(X, A)`.** A relative class dying in `H^{n+1}(X)` is a
connecting image. -/
theorem relLES_exact_rel (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : relCohomology R X A (n + 1)) (ha : (relToAbs R X A (n + 1)).hom a = 0) :
    ∃ b : (cochainCx R (TopCat.of A)).homology n, (relDelta R X A n).hom b = a :=
  (ShortComplex.moduleCat_exact_iff _).1
    ((pairShortExact R X A).homology_exact₁ n (n + 1) rfl) a ha

/-! ## 4. The two standard isomorphism criteria -/

/-- If the absolute cohomology of `X` vanishes in degrees `n` and `n+1`, the
connecting map `δ : H^n(A) ⟶ H^{n+1}(X, A)` is an isomorphism. -/
theorem isIso_relDelta (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (h₁ : IsZero ((cochainCx R X).homology n))
    (h₂ : IsZero ((cochainCx R X).homology (n + 1))) :
    IsIso (relDelta R X A n) := by
  have hmono : Mono (relDelta R X A n) :=
    ((pairShortExact R X A).homology_exact₃ n (n + 1) rfl).mono_g (h₁.eq_of_src _ _)
  have hepi : Epi (relDelta R X A n) :=
    ((pairShortExact R X A).homology_exact₁ n (n + 1) rfl).epi_f (h₂.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The connecting isomorphism `H^n(A) ≅ H^{n+1}(X, A)` under the two vanishing
hypotheses of `isIso_relDelta`. -/
def relDeltaIso (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (h₁ : IsZero ((cochainCx R X).homology n))
    (h₂ : IsZero ((cochainCx R X).homology (n + 1))) :
    (cochainCx R (TopCat.of A)).homology n ≅ relCohomology R X A (n + 1) :=
  haveI := isIso_relDelta R X A n h₁ h₂
  asIso (relDelta R X A n)

/-- If the cohomology of the subspace `A` vanishes in degrees `n` and `n+1`, then
`j^* : H^{n+1}(X, A) ⟶ H^{n+1}(X)` is an isomorphism. -/
theorem isIso_relToAbs (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (h₁ : IsZero ((cochainCx R (TopCat.of A)).homology n))
    (h₂ : IsZero ((cochainCx R (TopCat.of A)).homology (n + 1))) :
    IsIso (relToAbs R X A (n + 1)) := by
  have hmono : Mono (relToAbs R X A (n + 1)) :=
    ((pairShortExact R X A).homology_exact₁ n (n + 1) rfl).mono_g (h₁.eq_of_src _ _)
  have hepi : Epi (relToAbs R X A (n + 1)) :=
    ((pairShortExact R X A).homology_exact₂ (n + 1)).epi_f (h₂.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The isomorphism `H^{n+1}(X, A) ≅ H^{n+1}(X)` under the two vanishing
hypotheses of `isIso_relToAbs`. -/
def relToAbsIso (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (h₁ : IsZero ((cochainCx R (TopCat.of A)).homology n))
    (h₂ : IsZero ((cochainCx R (TopCat.of A)).homology (n + 1))) :
    relCohomology R X A (n + 1) ≅ (cochainCx R X).homology (n + 1) :=
  haveI := isIso_relToAbs R X A n h₁ h₂
  asIso (relToAbs R X A (n + 1))

/-! ## 5. The empty subspace -/

/-- No singular simplex has image inside the empty set (the standard simplex is
nonempty, its barycenter being a point of it). -/
theorem not_isSubordinate_empty (n : ℕ) (σ : singularSimplices X n) :
    ¬ IsSubordinate (∅ : Set X) σ := fun h =>
  (h (Set.mem_range_self (deltaBarycenter n))).elim

theorem relCochainSubmodule_empty (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    relCochainSubmodule R X (∅ : Set X) n = ⊤ := by
  refine eq_top_iff.2 ?_
  intro φ _ σ hσ
  exact ((not_isSubordinate_empty n σ) hσ).elim

instance isIso_relInclusion_empty_f (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    IsIso ((relInclusion R X (∅ : Set X)).f n) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab => Subtype.ext hab, ?_⟩
  intro φ
  exact ⟨⟨φ, by rw [relCochainSubmodule_empty]; trivial⟩, rfl⟩

instance isIso_relInclusion_empty (R : Type) [CommRing R] (X : TopCat.{0}) :
    IsIso (relInclusion R X (∅ : Set X)) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **`H^n(X, ∅) ≅ H^n(X)`.** -/
def relEmptyIso (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    relCohomology R X (∅ : Set X) n ≅ (cochainCx R X).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (asIso (relInclusion R X (∅ : Set X)))

end

end GroupApproximation.CharClass
