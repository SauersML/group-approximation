import GroupApproximation.CharClass.RelativeExcision
import GroupApproximation.CharClass.CupVanishSmallAnn
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative Mayer–Vietoris at cochain level: splitting a relative cocycle

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4).

`CharClass/LIXKCount.lean`'s `LocalSplit` obligation is `x = ∑_i ρ_i (x_i)`, where `ρ_i` is
relative pullback along the identity of `N` seen as a map of pairs
`(N, N ∖ Z) → (N, N ∖ {z_i})`.  Its proof reduces, by induction on the punctures, to the
two-set case: for opens `A, B` with `A ∪ B = X`,

```text
   H^n(X, A) ⊕ H^n(X, B) ⟶ H^n(X, A ∩ B)   is surjective.
```

This file proves that at **cochain level**, which is where all of its content is: a
relative cocycle of `(X, A ∩ B)` is the sum of a relative cocycle of `(X, A)` and one of
`(X, B)`.

## Why this is not excision to disjoint balls

`sp-design` §4.2 item 3 proposed excision to `k+1` disjoint balls, which needs a metric, a
disjointness argument, and a splitting of a *relative* group over a disjoint union.  None of
that appears here.  The construction is:

* **Split the cochain.**  `relKeep A` is the idempotent on chains that keeps the simplices
  subordinate to `A` and kills the others — `relRetract` followed by the pushforward along
  `A ↪ X`, both already in `CharClass/RelativeCochains.lean` and already generic in the
  coefficient ring.  Then `splitKeep φ := relKeep A ≫ φ` kills every `B`-simplex, because a
  simplex in both `A` and `B` is in `A ∩ B` where `φ` vanishes; and `splitDrop φ := φ −
  splitKeep φ` kills every `A`-simplex by construction.  **No subdivision, no cover
  hypothesis, no geometry**: this half is `splitDrop_mem` and `splitKeep_mem` below.
* **Correct them to cocycles.**  The two halves are not cocycles, but
  `δ(splitDrop φ) = −δ(splitKeep φ)` when `δφ = 0`, so that coboundary lies in
  `C^{n+1}(X, A) ∩ C^{n+1}(X, B)`, which is exactly the cochains vanishing on every
  `{A,B}`-**small** simplex.  Acyclicity of the small-annihilator complex — the single
  geometric input, and the same one excision consumes — writes it as `δγ` with `γ` itself
  small, and `γ` then lies in both relative submodules.  Replace `α := splitDrop φ − γ`,
  `β := splitKeep φ + γ`.

This is where `A ∪ B = X` enters, and it enters exactly once, through
`RelativeSmallChains.smallAnnComplex_acyclic`.

## Genericity

Everything through `splitKeep_mem` is generic in `[CommRing R]`.  The correction step needs
the acyclicity of the small-annihilator complex, which at this pin is proved only at
`ZMod 2` (`RelativeSmallChains.smallAnnComplex_acyclic`), so `exists_relCocycle_split` is
stated there; the generic version `exists_relCocycle_split_of_acyclic` takes the acyclicity
as a hypothesis and is the one to instantiate once `sp-coeff` generalises that file.

## Main declarations

* `relKeep`, `relKeep_generator`, `relKeep_generator_of_not` — the idempotent.
* `splitDrop`, `splitKeep`, `splitDrop_mem`, `splitKeep_mem` — the cochain split, generic.
* `coboundary_splitDrop_mem_smallAnn` — the obstruction is small.
* `exists_relCocycle_split_of_acyclic`, `exists_relCocycle_split` — **the theorem**.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace LIXKRelMV

open CategoryTheory Limits AlgebraicTopology TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

set_option linter.unusedSectionVars false

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 0. Two evaluation lemmas the vendored layer does not have -/

theorem cochainEval_sub (p : ℕ) (φ ψ : singularCochainGroup R X p)
    (τ : singularSimplices X p) :
    cochainEval p (φ - ψ) τ = cochainEval p φ τ - cochainEval p ψ τ := by
  unfold cochainEval
  simp

theorem cochainEval_neg (p : ℕ) (φ : singularCochainGroup R X p)
    (τ : singularSimplices X p) :
    cochainEval p (-φ) τ = - cochainEval p φ τ := by
  unfold cochainEval
  simp

theorem cochainCoboundary_sub (p : ℕ) (φ ψ : singularCochainGroup R X p) :
    cochainCoboundary R X p (φ - ψ)
      = cochainCoboundary R X p φ - cochainCoboundary R X p ψ := by
  unfold cochainCoboundary
  exact map_sub _ _ _

theorem cochainCoboundary_add' (p : ℕ) (φ ψ : singularCochainGroup R X p) :
    cochainCoboundary R X p (φ + ψ)
      = cochainCoboundary R X p φ + cochainCoboundary R X p ψ := by
  unfold cochainCoboundary
  exact map_add _ _ _

/-! ## 1. The idempotent that keeps the `A`-simplices -/

/-- **Keep the simplices subordinate to `A`, kill the rest.**  This is `relRetract`
followed by the pushforward along `A ↪ X`; both halves are already in the tree and both are
generic in the coefficient ring. -/
def relKeep (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    singularChainGroup R X n ⟶ singularChainGroup R X n :=
  relRetract R X A n ≫ singularChainMap R (sInclusion A) n

theorem relKeep_generator (A : Set X) (n : ℕ) {σ : singularSimplices X n}
    (hσ : IsSubordinate A σ) :
    (relKeep R X A n).hom (chainGenerator R X n σ) = chainGenerator R X n σ := by
  obtain ⟨τ, rfl⟩ := exists_pushSimplex_of_subordinate A n hσ
  rw [relKeep, ModuleCat.comp_apply, relRetract_generator A n τ,
    singularChainMap_generator R (sInclusion A) n τ]

theorem relKeep_generator_of_not (A : Set X) (n : ℕ) {σ : singularSimplices X n}
    (hσ : ¬ IsSubordinate A σ) :
    (relKeep R X A n).hom (chainGenerator R X n σ) = 0 := by
  rw [relKeep, ModuleCat.comp_apply, relRetract_generator_of_not A n hσ, map_zero]

/-! ## 2. The cochain split, generic in the coefficient ring -/

/-- The part of `φ` supported on the `A`-simplices. -/
def splitKeep (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : singularCochainGroup R X n) : singularCochainGroup R X n :=
  relKeep R X A n ≫ φ

/-- The rest of `φ`.  It vanishes on the `A`-simplices by construction. -/
def splitDrop (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (φ : singularCochainGroup R X n) : singularCochainGroup R X n :=
  φ - splitKeep R X A n φ

theorem splitDrop_add_splitKeep (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n) :
    splitDrop R X A n φ + splitKeep R X A n φ = φ := by
  rw [splitDrop, sub_add_cancel]

theorem cochainEval_splitKeep (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n)
    (σ : singularSimplices X n) :
    cochainEval n (splitKeep R X A n φ) σ
      = φ.hom ((relKeep R X A n).hom (chainGenerator R X n σ)) := rfl

theorem splitKeep_eval_of_subordinate (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n)
    {σ : singularSimplices X n} (hσ : IsSubordinate A σ) :
    cochainEval n (splitKeep R X A n φ) σ = cochainEval n φ σ := by
  rw [cochainEval_splitKeep, relKeep_generator A n hσ]
  rfl

theorem splitKeep_eval_of_not (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n)
    {σ : singularSimplices X n} (hσ : ¬ IsSubordinate A σ) :
    cochainEval n (splitKeep R X A n φ) σ = 0 := by
  rw [cochainEval_splitKeep, relKeep_generator_of_not A n hσ, map_zero]

/-- **The `A`-half really is a relative cochain of `(X, A)`**, for any `φ` whatever. -/
theorem splitDrop_mem (A : Set X) (n : ℕ) (φ : singularCochainGroup R X n) :
    splitDrop R X A n φ ∈ relCochainSubmodule R X A n := by
  intro σ hσ
  rw [splitDrop, cochainEval_sub, splitKeep_eval_of_subordinate A n φ hσ, sub_self]

/-- **The `B`-half really is a relative cochain of `(X, B)`.**  This is the one step that
uses `φ ∈ C^n(X, A ∩ B)`: a simplex lying in both `A` and `B` lies in `A ∩ B`, where `φ`
vanishes. -/
theorem splitKeep_mem (A B : Set X) (n : ℕ) {φ : singularCochainGroup R X n}
    (hφ : φ ∈ relCochainSubmodule R X (A ∩ B) n) :
    splitKeep R X A n φ ∈ relCochainSubmodule R X B n := by
  intro σ hσ
  by_cases hA : IsSubordinate A σ
  · rw [splitKeep_eval_of_subordinate A n φ hA]
    exact hφ σ (Set.subset_inter hA hσ)
  · exact splitKeep_eval_of_not A n φ hA

/-! ## 3. The obstruction is small -/

variable (U V : Opens X) (hUV : U ⊔ V = ⊤)

/-- The `V`-companion of `RelativeExcision.smallAnn_le_rel`. -/
theorem smallAnn_le_rel_right (R : Type) [CommRing R] (n : ℕ) :
    smallAnnSubmodule R X (twoSetCover U V hUV) n ≤ relCochainSubmodule R X (V : Set X) n :=
  fun _ hφ σ hσ => hφ σ (isSmallSimplex_of_subordinate_right U V hUV hσ)

/-- **The coboundary of the `A`-half kills every small simplex.**  It lies in
`C^{n+1}(X, U)` by construction, and in `C^{n+1}(X, V)` because it is the negative of the
coboundary of the `B`-half; a small simplex is subordinate to one of the two. -/
theorem coboundary_splitDrop_mem_smallAnn (n : ℕ) {φ : singularCochainGroup R X n}
    (hφ : φ ∈ relCochainSubmodule R X ((U : Set X) ∩ (V : Set X)) n)
    (hδ : cochainCoboundary R X n φ = 0) :
    cochainCoboundary R X n (splitDrop R X (U : Set X) n φ)
      ∈ smallAnnSubmodule R X (twoSetCover U V hUV) (n + 1) := by
  have hneg : cochainCoboundary R X n (splitDrop R X (U : Set X) n φ)
      = - cochainCoboundary R X n (splitKeep R X (U : Set X) n φ) := by
    rw [splitDrop, cochainCoboundary_sub, hδ, zero_sub]
  intro σ hσ
  rcases subordinate_or_of_isSmallSimplex U V hUV hσ with hU | hV
  · exact cochainCoboundary_mem_relCochainSubmodule R (U : Set X) n _
      (splitDrop_mem (U : Set X) n φ) σ hU
  · rw [hneg, cochainEval_neg]
    rw [cochainCoboundary_mem_relCochainSubmodule R (V : Set X) n _
      (splitKeep_mem (U : Set X) (V : Set X) n hφ) σ hV, neg_zero]

/-! ## 4. The split into cocycles -/

/-- **Relative Mayer–Vietoris, cochain level, over an abstract acyclicity input.**

A relative cocycle of `(X, U ∩ V)` is the sum of a relative cocycle of `(X, U)` and one of
`(X, V)`.  `hacyclic` is the only geometric input and it is where `U ⊔ V = ⊤` is used. -/
theorem exists_relCocycle_split_of_acyclic (n : ℕ)
    (hacyclic : ∀ w : smallAnnSubmodule R X (twoSetCover U V hUV) (n + 1),
      (smallAnnD R X (twoSetCover U V hUV) (n + 1)).hom w = 0 →
      ∃ z : smallAnnSubmodule R X (twoSetCover U V hUV) n,
        (smallAnnD R X (twoSetCover U V hUV) n).hom z = w)
    {φ : singularCochainGroup R X n}
    (hφ : φ ∈ relCochainSubmodule R X ((U : Set X) ∩ (V : Set X)) n)
    (hδ : cochainCoboundary R X n φ = 0) :
    ∃ α β : singularCochainGroup R X n,
      α ∈ relCochainSubmodule R X (U : Set X) n ∧
        β ∈ relCochainSubmodule R X (V : Set X) n ∧
        cochainCoboundary R X n α = 0 ∧
        cochainCoboundary R X n β = 0 ∧
        α + β = φ := by
  have hmem : cochainCoboundary R X n (splitDrop R X (U : Set X) n φ)
      ∈ smallAnnSubmodule R X (twoSetCover U V hUV) (n + 1) :=
    coboundary_splitDrop_mem_smallAnn U V hUV n hφ hδ
  have hcocy : (smallAnnD R X (twoSetCover U V hUV) (n + 1)).hom
      (⟨cochainCoboundary R X n (splitDrop R X (U : Set X) n φ), hmem⟩ :
        smallAnnSubmodule R X (twoSetCover U V hUV) (n + 1)) = 0 :=
    Subtype.ext (cochainCoboundary_cochainCoboundary' R X n _)
  obtain ⟨γ, hγ⟩ := hacyclic _ hcocy
  have hγval : cochainCoboundary R X n (γ : singularCochainGroup R X n)
      = cochainCoboundary R X n (splitDrop R X (U : Set X) n φ) :=
    congrArg Subtype.val hγ
  refine ⟨splitDrop R X (U : Set X) n φ - (γ : singularCochainGroup R X n),
    splitKeep R X (U : Set X) n φ + (γ : singularCochainGroup R X n), ?_, ?_, ?_, ?_, ?_⟩
  · exact Submodule.sub_mem _ (splitDrop_mem (U : Set X) n φ)
      (smallAnn_le_rel U V hUV R n γ.2)
  · exact Submodule.add_mem _ (splitKeep_mem (U : Set X) (V : Set X) n hφ)
      (smallAnn_le_rel_right U V hUV R n γ.2)
  · rw [cochainCoboundary_sub, hγval, sub_self]
  · rw [cochainCoboundary_add', hγval, splitDrop, cochainCoboundary_sub, hδ, zero_sub,
      add_neg_cancel]
  · rw [sub_add_add_cancel, splitDrop_add_splitKeep]

include hUV in
/-- **Relative Mayer–Vietoris, cochain level, at mod-2 coefficients.**  The acyclicity
input is `CupVanishSmallAnn.exists_smallAnn_preimage`, which is
`RelativeSmallChains.smallAnnComplex_acyclic` in element form.

`include hUV in` is not decoration: the statement below never mentions `hUV`, and a section
variable is bound only when the *statement* mentions it, so without the `include` the proof
body refers to a name that is not in scope. -/
theorem exists_relCocycle_split (n : ℕ)
    {φ : singularCochainGroup (ZMod 2) X n}
    (hφ : φ ∈ relCochainSubmodule (ZMod 2) X ((U : Set X) ∩ (V : Set X)) n)
    (hδ : cochainCoboundary (ZMod 2) X n φ = 0) :
    ∃ α β : singularCochainGroup (ZMod 2) X n,
      α ∈ relCochainSubmodule (ZMod 2) X (U : Set X) n ∧
        β ∈ relCochainSubmodule (ZMod 2) X (V : Set X) n ∧
        cochainCoboundary (ZMod 2) X n α = 0 ∧
        cochainCoboundary (ZMod 2) X n β = 0 ∧
        α + β = φ :=
  exists_relCocycle_split_of_acyclic U V hUV n
    (fun w hw => exists_smallAnn_preimage X (twoSetCover U V hUV) n w hw) hφ hδ

end LIXKRelMV

/-! Audited on every build. -/

#audit_axioms LIXKRelMV.splitDrop_mem
#audit_axioms LIXKRelMV.splitKeep_mem
#audit_axioms LIXKRelMV.exists_relCocycle_split

end GroupApproximation.CharClass
