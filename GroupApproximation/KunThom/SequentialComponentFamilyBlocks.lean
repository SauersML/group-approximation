import GroupApproximation.KunThom.SequentialComponentFamily
import GroupApproximation.KunThom.BisectionActualDefect

/-!
# The objects of the component family as blocks of the ambient model

`objectBlocks D hT enum n` presents the objects of `componentFamily` as a
`BlockPatching.BlockEmbedding` of the ambient model: an object is placed by
`objectEmbedding`, and distinct objects lie in distinct components, which are
disjoint.  `objectBlockAction D hT enum n` pairs the ambient labels of `T` with
the completed labels on the objects.

* `uncovered_objectBlocks_negligible`: the ambient points lying in no object
  have negligible mass.  A point is uncovered only if its component is not good
  at the diagonal level, or it is one of the pruned points of its component.
* `compatFailure_sum_negligible`: for every label of `T`, the points where an
  object label and the ambient label disagree have negligible total mass.

These are the `huncovered` and `hcompat` hypotheses of
`vanishing_commutator_patch_of_candidates`.
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open scoped BigOperators
open BlockPatching

/-- A point lying in two indexed blocks determines the block. -/
theorem blockIndex_eq_of_mem {Y : FiniteModel} (P : BlockStructure Y) {C C' : BlockIndex P}
    {y : Y} (hC : y ∈ C.block) (hC' : y ∈ C'.block) : C = C' := by
  have h1 : P.block y = C.block := by
    have hmem : y ∈ P.block (BlockIndex.representative P C) := by
      rw [BlockIndex.block_representative]
      exact hC
    exact (P.eq_of_mem (BlockIndex.representative P C) y hmem).trans
      (BlockIndex.block_representative P C)
  have h2 : P.block y = C'.block := by
    have hmem : y ∈ P.block (BlockIndex.representative P C') := by
      rw [BlockIndex.block_representative]
      exact hC'
    exact (P.eq_of_mem (BlockIndex.representative P C') y hmem).trans
      (BlockIndex.block_representative P C')
  exact Subtype.ext (h1.symm.trans h2)

variable {K : Type} [Group K] {S : SoficApproximation K} {T : Finset K}
variable (D : ExpanderDecomposition S T)

/-- The objects as blocks of the ambient model. -/
noncomputable def objectBlocks (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) :
    BlockEmbedding (S.model n) (objectIndex D enum n) where
  model := objectModel D hT enum n
  embed := objectEmbedding D hT enum n
  embed_injective := objectEmbedding_injective D hT enum n
  embed_disjoint := by
    intro C C' x z hxz
    apply Subtype.ext
    refine blockIndex_eq_of_mem (D.blocks n) (objectEmbedding_mem D hT enum n C x) ?_
    rw [hxz]
    exact objectEmbedding_mem D hT enum n C' z

/-- The ambient labels of `T` together with the completed labels on the objects. -/
noncomputable def objectBlockAction (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) :
    BlockAction (objectBlocks D hT enum n) T where
  act s := S.map n s.1
  blockAct C s := objectAction D hT enum n C s.1

/-! ### Uncovered points -/

/-- The component through a point. -/
def componentOf (n : ℕ) (y : S.model n) : D.componentIndex n :=
  ⟨(D.blocks n).block y, (D.blocks n).block_mem_blocksFinset y⟩

theorem mem_componentOf (n : ℕ) (y : S.model n) : y ∈ (componentOf D n y).block :=
  (D.blocks n).self_mem y

open Classical in
/-- The points of a component that no object covers: the whole component if it
is not good at the diagonal level, and its pruned points otherwise. -/
noncomputable def lostPoints (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (C : D.componentIndex n) : Finset (S.model n) :=
  if IsGoodAt D enum (level D enum n) n C then
    (prunedSet D hT n C).map (Function.Embedding.subtype _)
  else C.block

theorem uncovered_subset_biUnion (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) :
    (objectBlocks D hT enum n).uncovered ⊆
      Finset.univ.biUnion (lostPoints D hT enum n) := by
  classical
  intro y hy
  rw [BlockPatching.BlockEmbedding.mem_uncovered] at hy
  refine Finset.mem_biUnion.mpr ⟨componentOf D n y, Finset.mem_univ _, ?_⟩
  have hyC := mem_componentOf D n y
  unfold lostPoints
  split_ifs with hgood
  · by_contra hnot
    have hmem : (⟨y, hyC⟩ : indexedBlockModel (D.blocks n) (componentOf D n y)) ∈
        Finset.univ \ prunedSet D hT n (componentOf D n y) := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _,
        fun hU ↦ hnot (Finset.mem_map_of_mem (Function.Embedding.subtype _) hU)⟩
    exact hy ⟨componentOf D n y, hgood⟩ ⟨⟨y, hyC⟩, hmem⟩ rfl
  · exact hyC

theorem card_uncovered_objectBlocks_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) :
    ((objectBlocks D hT enum n).uncovered.card : ℝ) ≤ uncoveredMass D hT enum n := by
  classical
  have h1 := Finset.card_le_card (uncovered_subset_biUnion D hT enum n)
  have h2 : (Finset.univ.biUnion (lostPoints D hT enum n)).card ≤
      ∑ C : D.componentIndex n, (lostPoints D hT enum n C).card :=
    Finset.card_biUnion_le
  have h1R : ((objectBlocks D hT enum n).uncovered.card : ℝ) ≤
      (Finset.univ.biUnion (lostPoints D hT enum n)).card := by
    exact_mod_cast h1
  have h2R : ((Finset.univ.biUnion (lostPoints D hT enum n)).card : ℝ) ≤
      ∑ C : D.componentIndex n, ((lostPoints D hT enum n C).card : ℝ) := by
    exact_mod_cast h2
  have h4 : ∑ C : D.componentIndex n, ((lostPoints D hT enum n C).card : ℝ) =
      uncoveredMass D hT enum n := by
    unfold uncoveredMass badMass prunedMass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    unfold lostPoints
    split_ifs with hC
    · rw [Finset.card_map]
      ring
    · ring
  linarith

theorem uncovered_objectBlocks_negligible [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ((objectBlocks D hT enum n).uncovered.card : ℝ)) :=
  Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _)
    (fun n ↦ card_uncovered_objectBlocks_le D hT enum n)
    (uncoveredMass_negligible D hsymm hgen hT enum)

/-! ### Compatibility failures -/

/-- Compatibility failures of an object: completion disagreement of its
component plus its pruned points. -/
theorem card_compatFailure_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ)
    (C : objectIndex D enum n) (s : T) :
    ((objectBlockAction D hT enum n).compatFailure C s).card ≤
      (D.componentCompletionDisagreement n C.1 s.1).card + (prunedSet D hT n C.1).card :=
  card_objectAction_disagreement_le D hT enum n C s.1

open Classical in
/-- A nonnegative sum over the objects is at most the sum over all components. -/
theorem sum_objectIndex_le (enum : ℕ → K) (n : ℕ) (f : D.componentIndex n → ℝ)
    (hf : ∀ C, 0 ≤ f C) :
    ∑ C : objectIndex D enum n, f C.1 ≤ ∑ C : D.componentIndex n, f C := by
  calc ∑ C : objectIndex D enum n, f C.1 =
        ∑ C ∈ (Finset.univ : Finset (objectIndex D enum n)).image Subtype.val, f C :=
        (Finset.sum_image Subtype.coe_injective.injOn).symm
    _ ≤ ∑ C : D.componentIndex n, f C :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun C _ _ ↦ hf C

open Classical in
theorem sum_objectIndex_prunedSet_le (hT : T.Nonempty) (enum : ℕ → K) (n : ℕ) :
    ∑ C : objectIndex D enum n, ((prunedSet D hT n C.1).card : ℝ) ≤
      prunedMass D hT enum n := by
  have hnn : ∀ C : D.componentIndex n,
      0 ≤ (if IsGoodAt D enum (level D enum n) n C then
        ((prunedSet D hT n C).card : ℝ) else 0) := by
    intro C
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_refl 0
  have h := sum_objectIndex_le D enum n
    (fun C ↦ if IsGoodAt D enum (level D enum n) n C then
      ((prunedSet D hT n C).card : ℝ) else 0) hnn
  have hcongr : ∑ C : objectIndex D enum n, ((prunedSet D hT n C.1).card : ℝ) =
      ∑ C : objectIndex D enum n, (if IsGoodAt D enum (level D enum n) n C.1 then
        ((prunedSet D hT n C.1).card : ℝ) else 0) :=
    Finset.sum_congr rfl fun C _ ↦ (if_pos C.2).symm
  rw [hcongr]
  exact h

open Classical in
theorem compatFailure_sum_negligible [Infinite K] (hsymm : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set K) = ⊤) (hT : T.Nonempty) (enum : ℕ → K) (s : T) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : objectIndex D enum n,
        (((objectBlockAction D hT enum n).compatFailure C s).card : ℝ)) := by
  have hdis : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        ((D.componentCompletionDisagreement n C s.1).card : ℝ)) := by
    simpa only [ExpanderDecomposition.componentCompletionDisagreement] using
      D.componentCompletedAction_disagreement_sum_negligible hsymm hgen s.1
  refine Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_) (fun n ↦ ?_)
    (hdis.add (prunedMass_negligible D hT enum))
  · exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  · have hA : ∑ C : objectIndex D enum n,
        (((objectBlockAction D hT enum n).compatFailure C s).card : ℝ) ≤
          ∑ C : objectIndex D enum n,
            (((D.componentCompletionDisagreement n C.1 s.1).card : ℝ) +
              ((prunedSet D hT n C.1).card : ℝ)) :=
      Finset.sum_le_sum fun C _ ↦ by exact_mod_cast card_compatFailure_le D hT enum n C s
    rw [Finset.sum_add_distrib] at hA
    have hB : ∑ C : objectIndex D enum n,
        ((D.componentCompletionDisagreement n C.1 s.1).card : ℝ) ≤
          ∑ C : D.componentIndex n, ((D.componentCompletionDisagreement n C s.1).card : ℝ) :=
      sum_objectIndex_le D enum n
        (fun C ↦ ((D.componentCompletionDisagreement n C s.1).card : ℝ))
        fun _ ↦ Nat.cast_nonneg _
    have hC := sum_objectIndex_prunedSet_le D hT enum n
    show _ ≤ (∑ C : D.componentIndex n,
      ((D.componentCompletionDisagreement n C s.1).card : ℝ)) + prunedMass D hT enum n
    linarith

end SequentialComponentFamily
end GroupApproximation
