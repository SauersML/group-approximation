import GroupApproximation.KunThom.ComponentCountingRetainedMatchingSums
import GroupApproximation.Matching.MatchingPreparation

/-!
# The retained component matching along the approximation

Kun–Thom (arXiv:2608.06222, proof of Lemma 4.3) restrict the quantitative
component matching of the distinguished compressor to the retained components.
The omitted components and removed parts must have vanishing total weight.  The
block matching (`LocalCriterionData.acceptable_symmDiff_sum_negligible`,
`discardedComponentMass_negligible`) is stated at the shifted index
`matchingIndex n`, so everything here uses that index too.

The retained objects are given by an embedding of blocks and an injective
parent map into the `Γ`-components of the decomposition.  The only asymptotic
inputs are negligible removed mass and negligible mass of components carrying
no object.

* `matchingAcceptable` and `injOn_refineIndex_matching`: on the acceptable
  components at the shifted index, the dominant-target map is injective.
* `retained_symmDiff_negligible`: over the retained domain, the symmetric
  differences between translated objects and their retained matches have
  negligible total size.
* `retained_unmatched_weight_negligible`: the objects outside the retained domain
  have negligible total weight.
-/

namespace GroupApproximation
namespace LocalCriterionData

open scoped symmDiff
open RetainedMatching

universe u

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
variable (D : LocalCriterionData G Γ J)

/-- The acceptable components at the shifted matching index. -/
noncomputable abbrev matchingAcceptable (n : ℕ) :
    Finset (D.gammaDecomposition.componentIndex (D.matchingIndex n)) :=
  D.acceptableComponents (D.matchingIndex n) (D.matchingThreshold (D.matchingIndex n))

/-- The dominant-target map at the shifted matching index. -/
noncomputable abbrev matchingRefine (n : ℕ) :
    D.gammaDecomposition.componentIndex (D.matchingIndex n) →
      D.gammaDecomposition.componentIndex (D.matchingIndex n) :=
  D.gammaDecomposition.refineIndex (D.distinguishedPerm (D.matchingIndex n))

/-- The dominant-target map is injective on the acceptable components. -/
theorem injOn_refineIndex_matching (n : ℕ) :
    Set.InjOn (D.matchingRefine n) (D.matchingAcceptable n : Set _) := by
  intro B hB B' hB' h
  apply D.acceptableTargets_injOn n hB hB'
  show (D.matchingRefine n B).block = (D.matchingRefine n B').block
  rw [h]

/-- **Retained matching error, asymptotically.**  Over the retained domain, the
symmetric differences between translated objects and their retained matches have
negligible total size. -/
theorem retained_symmDiff_negligible {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockPatching.BlockEmbedding (D.approximation.model n) (I n))
    (parent : ∀ n, I n → D.gammaDecomposition.componentIndex n)
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hremoved : Negligible D.N fun n ↦
      ∑ i, (((parent n i).block \ (E n).objectImage i).card : ℝ)) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ i ∈ retainedDomain (parent (D.matchingIndex n)) (D.matchingRefine n)
          (D.matchingAcceptable n),
        ((((E (D.matchingIndex n)).objectImage i).image (D.distinguishedPerm (D.matchingIndex n)) ∆
          (E (D.matchingIndex n)).objectImage
            (retainedTarget (parent (D.matchingIndex n)) (D.matchingRefine n) i)).card : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ D.N (D.matchingIndex n) := fun n ↦ D.N_nonneg _
  have hremoved' : Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ i, (((parent (D.matchingIndex n) i).block \
        (E (D.matchingIndex n)).objectImage i).card : ℝ) :=
    hremoved.shift D.matchingStart
  refine Negligible.mono_nonneg hN
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    (D.acceptable_symmDiff_sum_negligible.add (Negligible.const_mul 2 hremoved'))
  have h := sum_card_retained_symmDiff_le (E (D.matchingIndex n)) (fun B ↦ B.block)
    (hparent (D.matchingIndex n)) (hsub (D.matchingIndex n)) (D.injOn_refineIndex_matching n)
    (D.distinguishedPerm (D.matchingIndex n))
  show _ ≤ (∑ B ∈ D.matchingAcceptable n,
      ((D.matchImage (D.matchingIndex n) B ∆ D.matchTarget (D.matchingIndex n) B).card : ℝ)) +
    2 * ∑ i, (((parent (D.matchingIndex n) i).block \
      (E (D.matchingIndex n)).objectImage i).card : ℝ)
  exact_mod_cast h

/-- **Unmatched weight, asymptotically.**  The objects outside the retained domain
have negligible total weight. -/
theorem retained_unmatched_weight_negligible {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockPatching.BlockEmbedding (D.approximation.model n) (I n))
    (parent : ∀ n, I n → D.gammaDecomposition.componentIndex n)
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hnoObject : Negligible D.N fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent n), (B.block.card : ℝ)) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ i ∈ Finset.univ \ retainedDomain (parent (D.matchingIndex n)) (D.matchingRefine n)
          (D.matchingAcceptable n),
        (Fintype.card ((E (D.matchingIndex n)).model i) : ℝ) := by
  have hN : ∀ n, (0 : ℝ) ≤ D.N (D.matchingIndex n) := fun n ↦ D.N_nonneg _
  have hdiscard : Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      D.discardedComponentMass (D.matchingIndex n) (D.matchingThreshold (D.matchingIndex n)) :=
    D.discardedComponentMass_negligible.shift D.matchingStart
  have hnoObject' : Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent (D.matchingIndex n)), (B.block.card : ℝ) :=
    hnoObject.shift D.matchingStart
  refine Negligible.mono_nonneg hN
    (fun n ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
    ((hdiscard.add hnoObject').add D.acceptable_symmDiff_sum_negligible)
  have h := sum_card_not_retainedDomain_le (E (D.matchingIndex n)) (fun B ↦ B.block)
    (hparent (D.matchingIndex n)) (hsub (D.matchingIndex n)) (D.injOn_refineIndex_matching n)
    (D.distinguishedPerm (D.matchingIndex n))
  show _ ≤ (∑ B ∈ Finset.univ \ D.matchingAcceptable n, (B.block.card : ℝ)) +
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent (D.matchingIndex n)), (B.block.card : ℝ) +
    ∑ B ∈ D.matchingAcceptable n,
      ((D.matchImage (D.matchingIndex n) B ∆ D.matchTarget (D.matchingIndex n) B).card : ℝ)
  exact_mod_cast h

end LocalCriterionData
end GroupApproximation
