import GroupApproximation.KunThom.SequentialComponentFamilyBlocks
import GroupApproximation.KunThom.ComponentCountingRetainedMatchingNegligible

/-!
# Companion data of the component family

What the consumers of `componentFamily` need besides its fields.

* `objectIndexFintype`, `componentFamilyIndexFintype`,
  `componentFamilyIndexDecidableEq`: finiteness and decidable equality of the
  object index, also through `(componentFamily ..).index n`.
* `componentFamily_scale_eventually`: every object scale `|model| / 18`
  eventually exceeds any bound.
* `objectParent`: the component of an object.  It is injective, and each
  object image lies in its parent block (`objectImage_subset_parent`).
* `removedMass_negligible` and `noObjectMass_negligible`: the pruned parts of
  parent blocks, and the components carrying no object, have negligible mass.
* `retained_symmDiff_negligible_of_componentFamily` and
  `retained_unmatched_weight_negligible_of_componentFamily`: the retained
  component matching of `ComponentCountingRetainedMatchingNegligible`,
  instantiated with these objects on the `Γ`-decomposition of a
  `LocalCriterionData`.
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open scoped BigOperators symmDiff
open BlockPatching

variable {K : Type} [Group K] {S : SoficApproximation K} {T : Finset K}
variable (D : ExpanderDecomposition S T)

/-! ### Finiteness and scales -/

open Classical in
/-- The objects at an index form a finite type. -/
noncomputable instance objectIndexFintype (enum : ℕ → K) (n : ℕ) :
    Fintype (objectIndex D enum n) :=
  Subtype.fintype _

/-- The family index is the object index, so it is finite. -/
noncomputable instance componentFamilyIndexFintype [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K)
    (henum : Function.Surjective enum) (n : ℕ) :
    Fintype ((componentFamily D hsymm hgen hT enum henum).index n) :=
  objectIndexFintype D enum n

/-- Decidable equality on the family index. -/
noncomputable instance componentFamilyIndexDecidableEq [Infinite K]
    (hsymm : ∀ t ∈ T, t⁻¹ ∈ T) (hgen : Subgroup.closure (T : Set K) = ⊤)
    (hT : T.Nonempty) (enum : ℕ → K) (henum : Function.Surjective enum) (n : ℕ) :
    DecidableEq ((componentFamily D hsymm hgen hT enum henum).index n) :=
  inferInstanceAs (DecidableEq (objectIndex D enum n))

/-- Object scales eventually exceed any bound; `M = 20` is the bound of the
cluster system. -/
theorem componentFamily_scale_eventually [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K)
    (henum : Function.Surjective enum) (M : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : (componentFamily D hsymm hgen hT enum henum).index n,
      M ≤ (componentFamily D hsymm hgen hT enum henum).scale n i := by
  obtain ⟨N, hN⟩ := objectModel_size D hsymm hgen hT enum (18 * M)
  refine ⟨N, fun n hn i ↦ ?_⟩
  have h : 18 * M ≤ Fintype.card (objectModel D hT enum n i) := hN n hn i
  show M ≤ Fintype.card (objectModel D hT enum n i) / 18
  omega

/-! ### Parents, removed mass and components without objects -/

/-- The component of an object. -/
def objectParent (enum : ℕ → K) (n : ℕ) (i : objectIndex D enum n) : D.componentIndex n :=
  i.1

theorem objectParent_injective (enum : ℕ → K) (n : ℕ) :
    Function.Injective (objectParent D enum n) :=
  Subtype.val_injective

theorem objectImage_subset_parent (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) :
    (objectBlocks D hT enum n).objectImage i ⊆ (objectParent D enum n i).block := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  exact objectEmbedding_mem D hT enum n i y

/-- The points of a parent block outside its object are pruned points. -/
theorem card_block_sdiff_objectImage_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) :
    ((objectParent D enum n i).block \ (objectBlocks D hT enum n).objectImage i).card ≤
      (prunedSet D hT n i.1).card := by
  have hsub : (objectParent D enum n i).block \ (objectBlocks D hT enum n).objectImage i ⊆
      (prunedSet D hT n i.1).map (Function.Embedding.subtype _) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxC, hxnot⟩ := hx
    by_contra hnot
    apply hxnot
    have hmem : (⟨x, hxC⟩ : indexedBlockModel (D.blocks n) i.1) ∈
        Finset.univ \ prunedSet D hT n i.1 := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _,
        fun hU ↦ hnot (Finset.mem_map_of_mem (Function.Embedding.subtype _) hU)⟩
    exact BlockPatching.BlockEmbedding.mem_objectImage (objectBlocks D hT enum n) i
      ⟨⟨x, hxC⟩, hmem⟩
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_map _)

theorem removedMass_negligible (hT : T.Nonempty) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ i : objectIndex D enum n,
        (((objectParent D enum n i).block \ (objectBlocks D hT enum n).objectImage i).card : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_) (fun n ↦ ?_)
    (prunedMass_negligible D hT enum)
  · exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  · refine le_trans (Finset.sum_le_sum fun i _ ↦ ?_) (sum_objectIndex_prunedSet_le D hT enum n)
    exact_mod_cast card_block_sdiff_objectImage_le D hT enum n i

theorem noObjectMass_negligible [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (objectParent D enum n), (B.block.card : ℝ) := by
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_) (fun n ↦ ?_)
    (badMass_negligible D hsymm hgen enum)
  · exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  · classical
    have hnot : ∀ B ∈ Finset.univ \ Finset.univ.image (objectParent D enum n),
        ¬ IsGoodAt D enum (level D enum n) n B := by
      intro B hB hgood
      rw [Finset.mem_sdiff] at hB
      exact hB.2 (Finset.mem_image.mpr ⟨⟨B, hgood⟩, Finset.mem_univ _, rfl⟩)
    calc ∑ B ∈ Finset.univ \ Finset.univ.image (objectParent D enum n), (B.block.card : ℝ)
        = ∑ B ∈ Finset.univ \ Finset.univ.image (objectParent D enum n),
            (if IsGoodAt D enum (level D enum n) n B then 0 else (B.block.card : ℝ)) :=
          Finset.sum_congr rfl fun B hB ↦ (if_neg (hnot B hB)).symm
      _ ≤ ∑ B : D.componentIndex n,
            (if IsGoodAt D enum (level D enum n) n B then 0 else (B.block.card : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun B _ _ ↦ by split_ifs <;> positivity
      _ = badMass D enum n := rfl

/-! ### The retained matching on the `Γ`-decomposition -/

section LocalCriterion

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]

theorem removedMass_negligible_of_localCriterion (L : LocalCriterionData G Γ J)
    (enum : ℕ → Γ) :
    Negligible L.N fun n ↦
      ∑ i : objectIndex L.gammaDecomposition enum n,
        (((objectParent L.gammaDecomposition enum n i).block \
          (objectBlocks L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum n).objectImage
            i).card : ℝ) :=
  removedMass_negligible L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum

theorem noObjectMass_negligible_of_localCriterion (L : LocalCriterionData G Γ J)
    (enum : ℕ → Γ) :
    Negligible L.N fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (objectParent L.gammaDecomposition enum n),
        (B.block.card : ℝ) := by
  haveI : Infinite Γ := L.setup.infiniteΓ
  exact noObjectMass_negligible L.gammaDecomposition L.setup.generatorsΓ_symmetric
    L.setup.generatorsΓ_generate enum

/-- **Retained matching error for the component family.** -/
theorem retained_symmDiff_negligible_of_componentFamily (L : LocalCriterionData G Γ J)
    (enum : ℕ → Γ) :
    Negligible (fun n ↦ L.N (L.matchingIndex n)) fun n ↦
      ∑ i ∈ RetainedMatching.retainedDomain
          (objectParent L.gammaDecomposition enum (L.matchingIndex n))
          (L.matchingRefine n) (L.matchingAcceptable n),
        ((((objectBlocks L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum
            (L.matchingIndex n)).objectImage i).image
              (L.distinguishedPerm (L.matchingIndex n)) ∆
          (objectBlocks L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum
            (L.matchingIndex n)).objectImage
            (RetainedMatching.retainedTarget
              (objectParent L.gammaDecomposition enum (L.matchingIndex n))
              (L.matchingRefine n) i)).card : ℝ) :=
  L.retained_symmDiff_negligible
    (objectBlocks L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum)
    (objectParent L.gammaDecomposition enum) (objectParent_injective L.gammaDecomposition enum)
    (objectImage_subset_parent L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum)
    (removedMass_negligible_of_localCriterion L enum)

/-- **Unmatched weight for the component family.** -/
theorem retained_unmatched_weight_negligible_of_componentFamily
    (L : LocalCriterionData G Γ J) (enum : ℕ → Γ) :
    Negligible (fun n ↦ L.N (L.matchingIndex n)) fun n ↦
      ∑ i ∈ Finset.univ \ RetainedMatching.retainedDomain
          (objectParent L.gammaDecomposition enum (L.matchingIndex n))
          (L.matchingRefine n) (L.matchingAcceptable n),
        (Fintype.card ((objectBlocks L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum
          (L.matchingIndex n)).model i) : ℝ) :=
  L.retained_unmatched_weight_negligible
    (objectBlocks L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum)
    (objectParent L.gammaDecomposition enum) (objectParent_injective L.gammaDecomposition enum)
    (objectImage_subset_parent L.gammaDecomposition ⟨1, L.setup.generatorsΓ_one⟩ enum)
    (noObjectMass_negligible_of_localCriterion L enum)

end LocalCriterion

end SequentialComponentFamily
end GroupApproximation
