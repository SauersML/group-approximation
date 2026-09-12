import GroupApproximation.CharClass.LIXKLocalSplit
import GroupApproximation.CharClass.LIXKStepCTwo
import GroupApproximation.CharClass.RelativeSubspaceIso
import GroupApproximation.CharClass.RelativeRangeKer
import GroupApproximation.Meta.AxiomGuard

/-!
# The `k`-zero Step C over `F₂`, with the split discharged and the local classes read off
# neighbourhoods

Lane `lix-oddside` of the stronger Problem LIX program
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4).

`CharClass/LIXKStepCTwo.lean`'s `topChernClass_ne_zero_kzero_two` takes two `k`-zero
obligations: the split `hsplit : LocalSplit …`, and `hx : ∀ i, xloc i ≠ 0` for the pieces
of that split.  `CharClass/LIXKLocalSplit.lean` proves the split exists.  This file turns the
second obligation into a statement about the class `x` itself.

## The local classes, read off neighbourhoods

For a set `B` containing the `i`-th zero and none of the others, restrict to `B`:

```text
  restrictTo B : Hⁿ(X, X ∖ Z) ⟶ Hⁿ(B, B ∖ Z).
```

A piece `ρⱼ(xⱼ)` with `j ≠ i` restricts to zero, because the identity of `B`, read as a map of
pairs `(B, B ∖ Z) → (B, B)`, factors the restriction, and `Hⁿ(B, B) = 0`
(`restrictTo_relPullback_id_eq_zero`).  So `restrictTo B x` is the restriction of `ρᵢ(xᵢ)`
alone, and **`restrictTo B x ≠ 0` forces `xᵢ ≠ 0`** (`xloc_ne_zero_of_restrictTo_ne_zero`).
Neither excision nor openness of `B` is used.

## Main declarations

* `restrictTo` — restriction of a relative class to a subspace.
* `restrictTo_relPullback_id_eq_zero` — a piece supported away from `B` restricts to zero.
* `xloc_ne_zero_of_restrictTo_ne_zero` — the local piece is nonzero if the local restriction is.
* `topChernClass_ne_zero_kzero_two_of_restrict` — **the `k`-zero Step C over `F₂`**, with the
  split gone and every per-zero hypothesis a statement about `x` near that zero.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace LIXKRelMV

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. Restriction to a subspace -/

/-- The inclusion of a subspace is a map of pairs `(B, B ∩ C) → (X, C)`. -/
theorem sInclusion_mapsTo_preimage (B C : Set X) :
    ∀ y ∈ (Subtype.val : ↥B → X) ⁻¹' C, (ConcreteCategory.hom (sInclusion B)) y ∈ C :=
  fun _ hy => hy

/-- **Restriction of a relative class to the subspace `B`.** -/
def restrictTo (R : Type) [CommRing R] (B C : Set X) (n : ℕ) :
    relCohomology R X C n ⟶
      relCohomology R (TopCat.of ↥B) ((Subtype.val : ↥B → X) ⁻¹' C) n :=
  relPullback R (sInclusion B) (sInclusion_mapsTo_preimage B C) n

/-- **A piece supported away from `B` restricts to zero.**  If every point of `B` lies in
`D`, the restriction to `B` of the pullback of a class of `(X, D)` along the identity factors
through `Hⁿ(B, B) = 0`. -/
theorem restrictTo_relPullback_id_eq_zero {C D : Set X} (B : Set X)
    (hCD : ∀ y ∈ C, (ConcreteCategory.hom (𝟙 X)) y ∈ D) (hBD : ∀ y ∈ B, y ∈ D) (n : ℕ)
    (v : relCohomology R X D n) :
    (restrictTo R B C n).hom ((relPullback R (𝟙 X) hCD n).hom v) = 0 := by
  have hBD' : ∀ y ∈ (Subtype.val : ↥B → X) ⁻¹' C,
      (ConcreteCategory.hom (sInclusion B)) y ∈ D := fun y _ => hBD y.1 y.2
  have hfg1 : ∀ y ∈ (Subtype.val : ↥B → X) ⁻¹' C,
      (ConcreteCategory.hom (sInclusion B ≫ 𝟙 X)) y ∈ D := fun y _ => hBD y.1 y.2
  have h₁ : ∀ y ∈ (Subtype.val : ↥B → X) ⁻¹' C,
      (ConcreteCategory.hom (𝟙 (TopCat.of ↥B))) y ∈ (Set.univ : Set ↥B) :=
    fun _ _ => Set.mem_univ _
  have h₂ : ∀ y ∈ (Set.univ : Set ↥B), (ConcreteCategory.hom (sInclusion B)) y ∈ D :=
    fun y _ => hBD y.1 y.2
  have hfg2 : ∀ y ∈ (Subtype.val : ↥B → X) ⁻¹' C,
      (ConcreteCategory.hom (𝟙 (TopCat.of ↥B) ≫ sInclusion B)) y ∈ D :=
    fun y _ => hBD y.1 y.2
  have e1 : relPullback R (𝟙 X) hCD n ≫ restrictTo R B C n
      = relPullback R (sInclusion B) hBD' n := by
    rw [restrictTo, ← relPullback_comp R (sInclusion B) (𝟙 X) _ hCD hfg1 n]
    exact relPullback_eq_of_eq R (Category.comp_id (sInclusion B)) hfg1 n
  have e2 : relPullback R (sInclusion B) hBD' n
      = relPullback R (sInclusion B) h₂ n ≫ relPullback R (𝟙 (TopCat.of ↥B)) h₁ n := by
    rw [← relPullback_comp R (𝟙 (TopCat.of ↥B)) (sInclusion B) h₁ h₂ hfg2 n]
    exact (relPullback_eq_of_eq R (Category.id_comp (sInclusion B)) hfg2 n).symm
  have hzero : (relPullback R (sInclusion B) h₂ n).hom v = 0 :=
    relCohomology_eq_zero_of_forall_mem (fun y => Set.mem_univ y) n _
  calc (restrictTo R B C n).hom ((relPullback R (𝟙 X) hCD n).hom v)
      = (relPullback R (𝟙 X) hCD n ≫ restrictTo R B C n).hom v := rfl
    _ = (relPullback R (sInclusion B) h₂ n ≫ relPullback R (𝟙 (TopCat.of ↥B)) h₁ n).hom v := by
        rw [e1, e2]
    _ = (relPullback R (𝟙 (TopCat.of ↥B)) h₁ n).hom ((relPullback R (sInclusion B) h₂ n).hom v) :=
        rfl
    _ = 0 := by rw [hzero, map_zero]

/-- **The local piece is nonzero if the local restriction is.**  For a split
`x = ∑ⱼ ρⱼ(xⱼ)` along the identity, and a set `B` containing none of the zeros other than the
`i`-th, `restrictTo B x ≠ 0` forces `xᵢ ≠ 0`. -/
theorem xloc_ne_zero_of_restrictTo_ne_zero {k : ℕ} {z : Fin k → X} {C : Set X}
    (hC : ∀ y, y ∈ C ↔ ∀ i, y ≠ z i) (n : ℕ) {x : relCohomology R X C n}
    {xloc : ∀ i, relCohomology R X ({z i}ᶜ : Set X) n}
    (hsplit : x = ∑ i, (relPullback R (𝟙 X) (mapsTo_compl_puncture hC i) n).hom (xloc i))
    (i : Fin k) {B : Set X} (hB : ∀ j, j ≠ i → z j ∉ B)
    (hx : (restrictTo R B C n).hom x ≠ 0) :
    xloc i ≠ 0 := by
  intro h0
  apply hx
  rw [hsplit, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hji : j = i
  · subst hji
    rw [h0, map_zero, map_zero]
  · refine restrictTo_relPullback_id_eq_zero B _ (fun y hy hyz => ?_) n _
    exact hB j hji ((Set.mem_singleton_iff.mp hyz) ▸ hy)

/-! ## 2. The `k`-zero Step C over `F₂`, split discharged -/

/-- `ρᵢ ≫ j = jᵢ`: naturality of `relToAbs` along the identity. -/
theorem relPullback_id_relToAbs {N : Type} [TopologicalSpace N] {A D : Set N}
    (h : ∀ y ∈ A, (ConcreteCategory.hom (𝟙 (TopCat.of N))) y ∈ D) (n : ℕ) :
    relPullback (ZMod 2) (𝟙 (TopCat.of N)) h n ≫ relToAbs (ZMod 2) (TopCat.of N) A n
      = relToAbs (ZMod 2) (TopCat.of N) D n := by
  have h' : relToAbs (ZMod 2) (TopCat.of N) D n ≫ RelativeSupport.absPull (𝟙 (TopCat.of N)) n
      = relPullback (ZMod 2) (𝟙 (TopCat.of N)) h n ≫ relToAbs (ZMod 2) (TopCat.of N) A n :=
    relToAbs_naturality (ZMod 2) (𝟙 (TopCat.of N)) h n
  rw [RelativeSupport.absPull_id_eq, Category.comp_id] at h'
  exact h'.symm

/-- **Step C's odd side with `k` zeros, over `F₂`, with the split discharged.**

The zeros `z₀, …, z_{k-1}` are distinct points of a T₁ space `N`, `C` is their complement,
and `x` is a class of `(N, C)`.  Every zero carries the one-zero Step C's line data
(punctured acyclicity, excision to the local model) and a set `B i` containing it and no other
zero, on which `x` restricts nontrivially.  If `k` is odd, `j(x) ≠ 0`. -/
theorem topChernClass_ne_zero_kzero_two_of_restrict {N : Type} [TopologicalSpace N]
    [T1Space N] {twoR r k : ℕ} (i₀ : Fin k) (z : Fin k → N) (hz : Function.Injective z)
    {C : Set N} (hC : ∀ y, y ∈ C ↔ ∀ i, y ≠ z i)
    (hac : ∀ i, PuncturedAcyclic N twoR (z i))
    (absLine : Nonempty (cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2))
    {chart : Fin k → ModuleCat.{0} (ZMod 2)}
    (exc : ∀ i, relCohomology (ZMod 2) (TopCat.of N) ({z i}ᶜ : Set N) twoR ≅ chart i)
    (chartIso : ∀ i, chart i ≅
      relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (x : relCohomology (ZMod 2) (TopCat.of N) C twoR)
    (B : Fin k → Set N) (hB : ∀ i j, j ≠ i → z j ∉ B i)
    (hloc : ∀ i, (restrictTo (ZMod 2) (X := TopCat.of N) (B i) C twoR).hom x ≠ 0)
    (hk : ((k : ℕ) : ZMod 2) ≠ 0) :
    (relToAbs (ZMod 2) (TopCat.of N) C twoR).hom x ≠ 0 := by
  obtain ⟨xloc, hsplit⟩ := exists_localSplit_two (X := TopCat.of N) z hz hC twoR x
  have hs : x = ∑ i, (relPullback (ZMod 2) (𝟙 (TopCat.of N))
      (mapsTo_compl_puncture hC i) twoR).hom (xloc i) := hsplit
  exact topChernClass_ne_zero_kzero_two i₀ z hac
    (relToAbs (ZMod 2) (TopCat.of N) C twoR)
    (fun i => relPullback (ZMod 2) (𝟙 (TopCat.of N)) (mapsTo_compl_puncture hC i) twoR)
    (fun i => relToAbs (ZMod 2) (TopCat.of N) ({z i}ᶜ : Set N) twoR)
    (fun i => relPullback_id_relToAbs (mapsTo_compl_puncture hC i) twoR)
    (fun i => absToSub (X := TopCat.of N) (ZMod 2) ({z i}ᶜ : Set N) twoR)
    (fun i => relLES_range_eq_ker (TopCat.of N) ({z i}ᶜ : Set N) twoR)
    absLine exc chartIso hsplit
    (fun i => xloc_ne_zero_of_restrictTo_ne_zero hC twoR hs i (hB i) (hloc i)) hk

end LIXKRelMV

/-! Audited on every build. -/

#audit_axioms LIXKRelMV.restrictTo_relPullback_id_eq_zero
#audit_axioms LIXKRelMV.xloc_ne_zero_of_restrictTo_ne_zero
#audit_axioms LIXKRelMV.topChernClass_ne_zero_kzero_two_of_restrict

end GroupApproximation.CharClass
