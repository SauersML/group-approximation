import GroupApproximation.KunThom.SequentialComponentFamilyBlocks
import GroupApproximation.KunThom.ComponentCountingRetainedMatching

/-!
# The sequential component family as retained objects of the matching

The retained component matching (`KunThom/ComponentCountingCompressorDomains`,
`KunThom/ComponentCountingCompressorImage`) runs over objects placed as blocks,
with an injective parent map into the components, objects inside their parents,
negligible removed mass and negligible mass of components carrying no object.
This file supplies those inputs for the objects of
`SequentialComponentFamily.componentFamily`, placed by `objectBlocks`.

* The parent map is `Subtype.val`, and `objectBlocks_objectImage_subset` places
  every object inside its component.
* `card_block_sdiff_objectImage_le` and `removedMass_objectBlocks_le`: the removed
  part of a component is its pruned set, so the removed mass is at most
  `prunedMass`.  `removedMass_objectBlocks_negligible` is its asymptotic form.
* `noObjectMass_objectBlocks_le`: the components carrying no object are the
  components that are not good, so their mass is at most `badMass`.
  `noObjectMass_objectBlocks_negligible` is its asymptotic form.
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open scoped BigOperators
open BlockPatching

variable {K : Type} [Group K] {S : SoficApproximation K} {T : Finset K}
variable (D : ExpanderDecomposition S T)

/-- Every object lies inside its component. -/
theorem objectBlocks_objectImage_subset (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) :
    (objectBlocks D hT enum n).objectImage i ⊆ i.1.block := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  exact objectEmbedding_mem D hT enum n i x

/-- The part of a component outside its object is at most its pruned set. -/
theorem card_block_sdiff_objectImage_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (i : objectIndex D enum n) :
    (i.1.block \ (objectBlocks D hT enum n).objectImage i).card ≤
      (prunedSet D hT n i.1).card := by
  have h₁ := Finset.card_sdiff_add_card_eq_card (objectBlocks_objectImage_subset D hT enum n i)
  have h₂ : ((objectBlocks D hT enum n).objectImage i).card =
      Fintype.card (objectModel D hT enum n i) :=
    (objectBlocks D hT enum n).card_objectImage i
  have h₃ := card_objectModel D hT enum n i
  omega

open Classical in
/-- **Removed mass.**  The components outside their objects weigh at most the
pruned mass. -/
theorem removedMass_objectBlocks_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) :
    ∑ i : objectIndex D enum n,
        ((i.1.block \ (objectBlocks D hT enum n).objectImage i).card : ℝ) ≤
      prunedMass D hT enum n :=
  (Finset.sum_le_sum fun i _ ↦ by
    exact_mod_cast card_block_sdiff_objectImage_le D hT enum n i).trans
    (sum_objectIndex_prunedSet_le D hT enum n)

open Classical in
/-- The removed mass is negligible. -/
theorem removedMass_objectBlocks_negligible (hT : T.Nonempty) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ i : objectIndex D enum n,
        ((i.1.block \ (objectBlocks D hT enum n).objectImage i).card : ℝ) :=
  Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    (fun n ↦ removedMass_objectBlocks_le D hT enum n) (prunedMass_negligible D hT enum)

open Classical in
/-- **Mass without objects.**  The components carrying no object are not good, so
they weigh at most the bad mass. -/
theorem noObjectMass_objectBlocks_le (enum : ℕ → K) (n : ℕ) :
    ∑ B ∈ Finset.univ \
        Finset.univ.image (Subtype.val : objectIndex D enum n → D.componentIndex n),
      (B.block.card : ℝ) ≤ badMass D enum n := by
  unfold badMass
  calc ∑ B ∈ Finset.univ \
          Finset.univ.image (Subtype.val : objectIndex D enum n → D.componentIndex n),
        (B.block.card : ℝ)
      = ∑ B ∈ Finset.univ \
          Finset.univ.image (Subtype.val : objectIndex D enum n → D.componentIndex n),
        (if IsGoodAt D enum (level D enum n) n B then 0 else (B.block.card : ℝ)) := by
        refine Finset.sum_congr rfl fun B hB ↦ ?_
        have hnot : ¬ IsGoodAt D enum (level D enum n) n B := by
          intro hgood
          exact (Finset.mem_sdiff.mp hB).2
            (Finset.mem_image.mpr ⟨⟨B, hgood⟩, Finset.mem_univ _, rfl⟩)
        simp [hnot]
    _ ≤ ∑ B : D.componentIndex n,
        (if IsGoodAt D enum (level D enum n) n B then 0 else (B.block.card : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ ↦ by split_ifs <;> positivity

open Classical in
/-- The mass without objects is negligible. -/
theorem noObjectMass_objectBlocks_negligible [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \
          Finset.univ.image (Subtype.val : objectIndex D enum n → D.componentIndex n),
        (B.block.card : ℝ) :=
  Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    (fun n ↦ noObjectMass_objectBlocks_le D enum n) (badMass_negligible D hsymm hgen enum)

end SequentialComponentFamily
end GroupApproximation
