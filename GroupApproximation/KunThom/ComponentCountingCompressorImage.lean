import GroupApproximation.KunThom.ComponentCountingCompressorDomains

/-!
# Weight outside the image of the retained matching

In the endgame of Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222, tex lines
1294–1313), the partial bisection is completed on negligible weight.  The objects
outside the image `π_n(D_n)` of the matching domain weigh `o(|Y_n|)`, and
`CountingEndgame.sum_compl_image_le` takes that weight as an input.

The parent of an object outside the image is not the dominant target of an
acceptable parent carrying an object.  The dominant-target map is injective on
acceptable components, and a target is at least as large as its source minus
their symmetric difference.  With the blocks partitioning the model, the weight
outside the image is at most the non-acceptable mass, the mass of blocks carrying
no object, and the block matching error.

* `RetainedMatching.sum_card_not_image_retainedDomain_le`: the finite bound.
* `sum_card_started_unimaged_le` and `started_unimaged_negligible`: the started
  form and its asymptotic form.
* `LocalCriterionData.componentBlock_sum_card`: the `Γ`-components partition the
  model.
* `LocalCriterionData.compressorDomain_unimaged_negligible` and
  `compressorDomains_unimaged_negligible`: the weight outside the image, for one
  compressor and for all of them.
-/

namespace GroupApproximation

open scoped symmDiff
open BlockPatching

universe u v

namespace RetainedMatching

section Finite

variable {Y : FiniteModel} {I : Type u} {J : Type v}

/-- **Weight outside the image of the retained matching.** -/
theorem sum_card_not_image_retainedDomain_le [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (E : BlockEmbedding Y I) (blk : J → Finset Y)
    (hpart : ∑ B, (blk B).card = Fintype.card Y) {parent : I → J}
    (hparent : Function.Injective parent) (hsub : ∀ i, E.objectImage i ⊆ blk (parent i))
    {τ : J → J} {Acc : Finset J} (hτ : Set.InjOn τ (Acc : Set J)) (u : Equiv.Perm Y) :
    ∑ j ∈ Finset.univ \ (retainedDomain parent τ Acc).image (retainedTarget parent τ),
        Fintype.card (E.model j) ≤
      ∑ B ∈ Finset.univ \ Acc, (blk B).card +
        ∑ B ∈ Finset.univ \ Finset.univ.image parent, (blk B).card +
          ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card := by
  -- the parent of an object outside the image is not a dominant target of an
  -- acceptable parent carrying an object
  have hstep1 : ∀ j ∈ Finset.univ \ (retainedDomain parent τ Acc).image (retainedTarget parent τ),
      parent j ∉ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent).image τ := by
    intro j hj hjT
    obtain ⟨B, hBS, hBj⟩ := Finset.mem_image.mp hjT
    obtain ⟨hBAcc, hBim⟩ := Finset.mem_filter.mp hBS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hBim
    have hi : i ∈ retainedDomain parent τ Acc :=
      (mem_retainedDomain parent τ Acc i).mpr ⟨hBAcc, j, hBj.symm⟩
    have hmatch : parent (retainedTarget parent τ i) = τ (parent i) :=
      isRetainedMatch_retainedTarget hi
    have hij : retainedTarget parent τ i = j := hparent (hmatch.trans hBj)
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_image.mpr ⟨i, hi, hij⟩)
  have hcard : ∀ j, Fintype.card (E.model j) ≤ (blk (parent j)).card := by
    intro j
    rw [← E.card_objectImage j]
    exact Finset.card_le_card (hsub j)
  have hstep2 : ∑ j ∈ Finset.univ \ (retainedDomain parent τ Acc).image (retainedTarget parent τ),
        Fintype.card (E.model j) ≤
      ∑ B ∈ Finset.univ \ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent).image τ,
        (blk B).card := by
    calc ∑ j ∈ Finset.univ \ (retainedDomain parent τ Acc).image (retainedTarget parent τ),
          Fintype.card (E.model j)
        ≤ ∑ j ∈ Finset.univ \ (retainedDomain parent τ Acc).image (retainedTarget parent τ),
          (blk (parent j)).card := Finset.sum_le_sum fun j _ ↦ hcard j
      _ = ∑ B ∈ (Finset.univ \ (retainedDomain parent τ Acc).image
            (retainedTarget parent τ)).image parent, (blk B).card :=
          (Finset.sum_image (f := fun B ↦ (blk B).card) fun i _ j _ hij ↦ hparent hij).symm
      _ ≤ ∑ B ∈ Finset.univ \ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent).image τ,
          (blk B).card := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro B hB
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hstep1 j hj⟩
          · intro _ _ _
            exact Nat.zero_le _
  have hstep3 : ∑ B ∈ Finset.univ \ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent).image τ,
        (blk B).card +
      ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent).image τ, (blk B).card =
      Fintype.card Y := by
    rw [Finset.sum_sdiff (Finset.subset_univ _), hpart]
  have hstep4 : ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent).image τ, (blk B).card =
      ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent), (blk (τ B)).card :=
    Finset.sum_image fun B hB C hC h ↦
      hτ (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hB)).1)
        (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hC)).1) h
  have hstep5 : ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent), (blk B).card ≤
      ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent),
          (((blk B).image u) ∆ blk (τ B)).card +
        ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent), (blk (τ B)).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun B _ ↦ card_le_card_symmDiff_add_card u (blk B) (blk (τ B))
  have hstep6 : ∑ B ∈ Finset.univ \ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent),
        (blk B).card +
      ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent), (blk B).card =
      Fintype.card Y := by
    rw [Finset.sum_sdiff (Finset.subset_univ _), hpart]
  have hsub7 : Finset.univ \ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent) ⊆
      (Finset.univ \ Acc) ∪ (Finset.univ \ Finset.univ.image parent) := by
    intro B hB
    have hnot := (Finset.mem_sdiff.mp hB).2
    by_cases hA : B ∈ Acc
    · refine Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun him ↦ hnot ?_⟩)
      exact Finset.mem_filter.mpr ⟨hA, him⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hA⟩)
  have h7a : ∑ B ∈ Finset.univ \ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent),
        (blk B).card ≤
      ∑ B ∈ (Finset.univ \ Acc) ∪ (Finset.univ \ Finset.univ.image parent), (blk B).card :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub7 fun _ _ _ ↦ Nat.zero_le _
  have h7b : ∑ B ∈ (Finset.univ \ Acc) ∪ (Finset.univ \ Finset.univ.image parent),
        (blk B).card +
      ∑ B ∈ (Finset.univ \ Acc) ∩ (Finset.univ \ Finset.univ.image parent), (blk B).card =
      ∑ B ∈ Finset.univ \ Acc, (blk B).card +
        ∑ B ∈ Finset.univ \ Finset.univ.image parent, (blk B).card :=
    Finset.sum_union_inter
  have hstep8 : ∑ B ∈ (Acc.filter fun B ↦ B ∈ Finset.univ.image parent),
        (((blk B).image u) ∆ blk (τ B)).card ≤
      ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ Nat.zero_le _
  omega

/-- The weight outside the image of the started matching, from the start on. -/
theorem sum_card_started_unimaged_le [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (E : BlockEmbedding Y I) (blk : J → Finset Y) (hpart : ∑ B, (blk B).card = Fintype.card Y)
    {parent : I → J} (hparent : Function.Injective parent)
    (hsub : ∀ i, E.objectImage i ⊆ blk (parent i))
    {τ : J → J} {Acc : Finset J} {start n : ℕ} (h : start ≤ n)
    (hτ : Set.InjOn τ (Acc : Set J)) (u : Equiv.Perm Y) :
    ∑ j ∈ Finset.univ \ (startedDomain parent τ Acc start n).image (retainedTarget parent τ),
        Fintype.card (E.model j) ≤
      ∑ B ∈ Finset.univ \ Acc, (blk B).card +
        ∑ B ∈ Finset.univ \ Finset.univ.image parent, (blk B).card +
          ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card := by
  rw [startedDomain_of_start parent τ Acc h]
  exact sum_card_not_image_retainedDomain_le E blk hpart hparent hsub hτ u

end Finite

/-- **Weight outside the image, asymptotically.**  The objects outside the image of
the started matching have negligible total weight. -/
theorem started_unimaged_negligible {Y : ℕ → FiniteModel} {I : ℕ → Type u}
    {J : ℕ → Type v} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Fintype (J n)]
    [∀ n, DecidableEq (J n)]
    (E : ∀ n, BlockEmbedding (Y n) (I n)) (blk : ∀ n, J n → Finset (Y n))
    (hpart : ∀ n, ∑ B, (blk n B).card = Fintype.card (Y n))
    {parent : ∀ n, I n → J n} (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ blk n (parent n i))
    {τ : ∀ n, J n → J n} {Acc : ∀ n, Finset (J n)} {start : ℕ}
    (hτ : ∀ n, start ≤ n → Set.InjOn (τ n) (Acc n : Set (J n)))
    (u : ∀ n, Equiv.Perm (Y n))
    (hdisc : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Acc n, ((blk n B).card : ℝ))
    (hnoObject : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent n), ((blk n B).card : ℝ))
    (hblk : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ j ∈ Finset.univ \ (startedDomain (parent n) (τ n) (Acc n) start n).image
          (retainedTarget (parent n) (τ n)),
        (Fintype.card ((E n).model j) : ℝ) := by
  refine Vanishing.squeeze_eventually ((hdisc.add hnoObject).add hblk) start
    fun n hn ↦ ⟨?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    show (∑ j ∈ Finset.univ \ (startedDomain (parent n) (τ n) (Acc n) start n).image
          (retainedTarget (parent n) (τ n)),
        (Fintype.card ((E n).model j) : ℝ)) ≤
      (∑ B ∈ Finset.univ \ Acc n, ((blk n B).card : ℝ)) +
        (∑ B ∈ Finset.univ \ Finset.univ.image (parent n), ((blk n B).card : ℝ)) +
          ∑ B ∈ Acc n, ((((blk n B).image (u n)) ∆ blk n (τ n B)).card : ℝ)
    exact_mod_cast sum_card_started_unimaged_le (E n) (blk n) (hpart n) (hparent n) (hsub n)
      hn (hτ n hn) (u n)

end RetainedMatching

namespace LocalCriterionData

open RetainedMatching

/-- The `Γ`-components partition the model. -/
theorem componentBlock_sum_card {G Γ J : Type} [Group G] [Group Γ] [Group J]
    (D : LocalCriterionData G Γ J) (n : ℕ) :
    ∑ B : D.gammaDecomposition.componentIndex n, B.block.card =
      Fintype.card (D.approximation.model n) :=
  BlockIndex.sum_card (D.gammaDecomposition.blocks n)

/-- **Weight outside the image of a compressor's retained matching.** -/
theorem compressorDomain_unimaged_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockEmbedding (D.approximation.model n) (I n))
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hnoObject : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent n), (B.block.card : ℝ))
    {t : G} (ht : t ∈ D.setup.compressors) :
    Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ j ∈ Finset.univ \ (D.compressorDomain parent ht n).image (D.compressorMatch parent t n),
        (Fintype.card ((E n).model j) : ℝ) := by
  have h := started_unimaged_negligible (Y := fun n ↦ D.approximation.model n)
    (J := fun n ↦ D.gammaDecomposition.componentIndex n) E (fun n B ↦ B.block)
    (fun n ↦ D.componentBlock_sum_card n) hparent hsub
    (τ := D.compressorRefine t) (Acc := D.compressorAcceptable ht)
    (start := (D.withDistinguished t ht).matchingStart)
    (fun _ hn ↦ D.compressorRefine_injOn ht hn) (fun n ↦ D.approximation.map n t)
    (D.compressorDiscarded_negligible ht) hnoObject (D.compressorBlock_symmDiff_negligible ht)
  exact h

/-- **Weight outside the images, for all compressors**, with
`Dom := D.compressorDomains parent` and `π := D.compressorMatch parent`. -/
theorem compressorDomains_unimaged_negligible {G Γ : Type} [Group G] [Group Γ]
    (D : LocalCriterionData G Γ PUnit.{1}) {I : ℕ → Type u} [∀ n, Fintype (I n)]
    [∀ n, DecidableEq (I n)]
    (E : ∀ n, BlockEmbedding (D.approximation.model n) (I n))
    {parent : ∀ n, I n → D.gammaDecomposition.componentIndex n}
    (hparent : ∀ n, Function.Injective (parent n))
    (hsub : ∀ n i, (E n).objectImage i ⊆ (parent n i).block)
    (hnoObject : Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
      ∑ B ∈ Finset.univ \ Finset.univ.image (parent n), (B.block.card : ℝ)) :
    ∀ q ∈ D.setup.compressors,
      Negligible (fun n ↦ (Fintype.card (D.approximation.model n) : ℝ)) fun n ↦
        ∑ j ∈ Finset.univ \ (D.compressorDomains parent q n).image (D.compressorMatch parent q n),
          (Fintype.card ((E n).model j) : ℝ) := by
  intro q hq
  refine (D.compressorDomain_unimaged_negligible E hparent hsub hnoObject hq).congr fun n ↦ ?_
  rw [D.compressorDomains_of_mem parent hq n]

end LocalCriterionData
end GroupApproximation
