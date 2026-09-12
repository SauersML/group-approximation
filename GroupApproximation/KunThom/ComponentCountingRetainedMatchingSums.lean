import GroupApproximation.KunThom.ComponentCountingRetainedMatching

/-!
# The retained component matching and its total errors

Kun and Thom (arXiv:2608.06222, proof of Lemma 4.3) restrict the component
matching of a compressor to the retained components, "deleting the pairs that
meet the omitted family".  This file makes that deletion explicit and bounds its
two costs.

Objects are retained subsets of parent blocks.  The parent map is injective.
`τ` is the dominant-target map of the blocks, injective on the acceptable
blocks `Acc`.

* `retainedDomain`: the objects with an acceptable parent whose dominant target is
  the parent of some object.  `retainedTarget` picks that object, and
  `isRetainedMatch_retainedTarget` and `injOn_retainedTarget` make the matching a
  partial injection.
* `sum_card_retained_symmDiff_le`: over the retained domain, the symmetric
  differences of translated objects and their matches add up to at most the block
  matching error over `Acc` plus twice the removed mass.
* `sum_card_not_retainedDomain_le`: the objects outside the retained domain weigh
  at most the blocks outside `Acc`, the blocks carrying no object, and the block
  matching error over `Acc`.
-/

namespace GroupApproximation
namespace RetainedMatching

open scoped symmDiff

universe u

variable {Y : FiniteModel} {I : Type u} {J : Type*}

/-- The objects with an acceptable parent whose dominant target is the parent of
some object. -/
noncomputable def retainedDomain [Fintype I] (parent : I → J) (τ : J → J) (Acc : Finset J) :
    Finset I := by
  classical
  exact Finset.univ.filter fun i ↦ parent i ∈ Acc ∧ ∃ j, parent j = τ (parent i)

theorem mem_retainedDomain [Fintype I] (parent : I → J) (τ : J → J) (Acc : Finset J) (i : I) :
    i ∈ retainedDomain parent τ Acc ↔ parent i ∈ Acc ∧ ∃ j, parent j = τ (parent i) := by
  classical
  simp [retainedDomain]

/-- The retained match of an object: an object whose parent is the dominant target
of its parent, when one exists. -/
noncomputable def retainedTarget (parent : I → J) (τ : J → J) (i : I) : I := by
  classical
  exact if h : ∃ j, parent j = τ (parent i) then Classical.choose h else i

theorem isRetainedMatch_retainedTarget [Fintype I] {parent : I → J} {τ : J → J}
    {Acc : Finset J} {i : I} (hi : i ∈ retainedDomain parent τ Acc) :
    IsRetainedMatch parent τ i (retainedTarget parent τ i) := by
  obtain ⟨_, h⟩ := (mem_retainedDomain parent τ Acc i).mp hi
  unfold retainedTarget
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The retained matching is injective on the retained domain. -/
theorem injOn_retainedTarget [Fintype I] {parent : I → J} (hparent : Function.Injective parent)
    {τ : J → J} {Acc : Finset J} (hτ : Set.InjOn τ (Acc : Set J)) :
    Set.InjOn (retainedTarget parent τ) (retainedDomain parent τ Acc : Set I) := by
  intro i hi i' hi' heq
  have hi₀ := isRetainedMatch_retainedTarget (Finset.mem_coe.mp hi)
  have hi'₀ := isRetainedMatch_retainedTarget (Finset.mem_coe.mp hi')
  rw [← heq] at hi'₀
  exact retainedMatch_unique_source hparent hτ
    ((mem_retainedDomain parent τ Acc i).mp (Finset.mem_coe.mp hi)).1
    ((mem_retainedDomain parent τ Acc i').mp (Finset.mem_coe.mp hi')).1 hi₀ hi'₀

/-- **Retained matching error.**  Over the retained domain, the symmetric
differences between translated objects and their retained matches add up to at
most the block matching error over the acceptable blocks plus twice the removed
mass. -/
theorem sum_card_retained_symmDiff_le [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (E : BlockPatching.BlockEmbedding Y I) (blk : J → Finset Y) {parent : I → J}
    (hparent : Function.Injective parent) (hsub : ∀ i, E.objectImage i ⊆ blk (parent i))
    {τ : J → J} {Acc : Finset J} (hτ : Set.InjOn τ (Acc : Set J)) (u : Equiv.Perm Y) :
    ∑ i ∈ retainedDomain parent τ Acc,
        (((E.objectImage i).image u) ∆ E.objectImage (retainedTarget parent τ i)).card ≤
      ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card +
        2 * ∑ i, (blk (parent i) \ E.objectImage i).card := by
  have hterm : ∀ i ∈ retainedDomain parent τ Acc,
      (((E.objectImage i).image u) ∆ E.objectImage (retainedTarget parent τ i)).card ≤
        (((blk (parent i)).image u) ∆ blk (τ (parent i))).card +
          (blk (parent i) \ E.objectImage i).card +
            (blk (parent (retainedTarget parent τ i)) \
              E.objectImage (retainedTarget parent τ i)).card := by
    intro i hi
    have hmatch : parent (retainedTarget parent τ i) = τ (parent i) :=
      isRetainedMatch_retainedTarget hi
    have h := card_image_symmDiff_le u (hsub i) (hsub (retainedTarget parent τ i))
    rw [hmatch] at h
    rw [hmatch]
    exact h
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have himg₁ : ∑ B ∈ (retainedDomain parent τ Acc).image parent,
        (((blk B).image u) ∆ blk (τ B)).card =
      ∑ i ∈ retainedDomain parent τ Acc,
        (((blk (parent i)).image u) ∆ blk (τ (parent i))).card :=
    Finset.sum_image fun i _ j _ hij ↦ hparent hij
  have h₁ : ∑ B ∈ (retainedDomain parent τ Acc).image parent,
        (((blk B).image u) ∆ blk (τ B)).card ≤
      ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      exact ((mem_retainedDomain parent τ Acc i).mp hi).1
    · intro _ _ _
      exact Nat.zero_le _
  have h₂ : ∑ i ∈ retainedDomain parent τ Acc, (blk (parent i) \ E.objectImage i).card ≤
      ∑ i, (blk (parent i) \ E.objectImage i).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
  have himg₃ : ∑ j ∈ (retainedDomain parent τ Acc).image (retainedTarget parent τ),
        (blk (parent j) \ E.objectImage j).card =
      ∑ i ∈ retainedDomain parent τ Acc, (blk (parent (retainedTarget parent τ i)) \
        E.objectImage (retainedTarget parent τ i)).card :=
    Finset.sum_image (injOn_retainedTarget hparent hτ)
  have h₃ : ∑ j ∈ (retainedDomain parent τ Acc).image (retainedTarget parent τ),
        (blk (parent j) \ E.objectImage j).card ≤
      ∑ i, (blk (parent i) \ E.objectImage i).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
  omega

/-- A translated block exceeds its dominant target by at most their symmetric
difference. -/
theorem card_le_card_symmDiff_add_card [DecidableEq Y] (u : Equiv.Perm Y) (B B' : Finset Y) :
    B.card ≤ ((B.image u) ∆ B').card + B'.card := by
  have h₂ : (B.image u).card = B.card := Finset.card_image_of_injective _ u.injective
  have h₃ : (B.image u).card ≤ (B.image u \ B').card + B'.card :=
    Finset.card_le_card_sdiff_add_card
  have h₄ : (B.image u \ B').card ≤ ((B.image u) ∆ B').card := by
    apply Finset.card_le_card
    intro y hy
    exact Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hy))
  omega

/-- **Unmatched weight.**  The objects outside the retained domain weigh at most
the blocks outside `Acc`, the blocks carrying no object, and the block matching
error over `Acc`. -/
theorem sum_card_not_retainedDomain_le [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (E : BlockPatching.BlockEmbedding Y I) (blk : J → Finset Y) {parent : I → J}
    (hparent : Function.Injective parent) (hsub : ∀ i, E.objectImage i ⊆ blk (parent i))
    {τ : J → J} {Acc : Finset J} (hτ : Set.InjOn τ (Acc : Set J)) (u : Equiv.Perm Y) :
    ∑ i ∈ Finset.univ \ retainedDomain parent τ Acc, Fintype.card (E.model i) ≤
      ∑ B ∈ Finset.univ \ Acc, (blk B).card +
        ∑ B ∈ Finset.univ \ Finset.univ.image parent, (blk B).card +
          ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card := by
  have hcard : ∀ i, Fintype.card (E.model i) ≤ (blk (parent i)).card := by
    intro i
    rw [← E.card_objectImage i]
    exact Finset.card_le_card (hsub i)
  -- objects whose parent is not acceptable
  have himgA : ∑ B ∈ ((Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ ¬ parent i ∈ Acc)).image parent, (blk B).card =
      ∑ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter (fun i ↦ ¬ parent i ∈ Acc),
        (blk (parent i)).card :=
    Finset.sum_image fun i _ j _ hij ↦ hparent hij
  have hleA : ∑ B ∈ ((Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ ¬ parent i ∈ Acc)).image parent, (blk B).card ≤
      ∑ B ∈ Finset.univ \ Acc, (blk B).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro _ _ _
      exact Nat.zero_le _
  have hsumA : ∑ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ ¬ parent i ∈ Acc), Fintype.card (E.model i) ≤
      ∑ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter (fun i ↦ ¬ parent i ∈ Acc),
        (blk (parent i)).card :=
    Finset.sum_le_sum fun i _ ↦ hcard i
  -- objects with an acceptable parent whose target block carries no object
  have hterm : ∀ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter (fun i ↦ parent i ∈ Acc),
      Fintype.card (E.model i) ≤
        (((blk (parent i)).image u) ∆ blk (τ (parent i))).card + (blk (τ (parent i))).card :=
    fun i _ ↦ (hcard i).trans (card_le_card_symmDiff_add_card u _ _)
  have hsumB := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsumB
  have himgB₁ : ∑ B ∈ ((Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ parent i ∈ Acc)).image parent, (((blk B).image u) ∆ blk (τ B)).card =
      ∑ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter (fun i ↦ parent i ∈ Acc),
        (((blk (parent i)).image u) ∆ blk (τ (parent i))).card :=
    Finset.sum_image fun i _ j _ hij ↦ hparent hij
  have hleB₁ : ∑ B ∈ ((Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ parent i ∈ Acc)).image parent, (((blk B).image u) ∆ blk (τ B)).card ≤
      ∑ B ∈ Acc, (((blk B).image u) ∆ blk (τ B)).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      exact (Finset.mem_filter.mp hi).2
    · intro _ _ _
      exact Nat.zero_le _
  have hinjB : Set.InjOn (fun i ↦ τ (parent i))
      ((Finset.univ \ retainedDomain parent τ Acc).filter (fun i ↦ parent i ∈ Acc) : Set I) := by
    intro i hi j hj hij
    exact hparent (hτ (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2 hij)
  have himgB₂ : ∑ B ∈ ((Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ parent i ∈ Acc)).image (fun i ↦ τ (parent i)), (blk B).card =
      ∑ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter (fun i ↦ parent i ∈ Acc),
        (blk (τ (parent i))).card :=
    Finset.sum_image hinjB
  have hleB₂ : ∑ B ∈ ((Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ parent i ∈ Acc)).image (fun i ↦ τ (parent i)), (blk B).card ≤
      ∑ B ∈ Finset.univ \ Finset.univ.image parent, (blk B).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨hi₁, hi₂⟩ := Finset.mem_filter.mp hi
      have hnot : i ∉ retainedDomain parent τ Acc := (Finset.mem_sdiff.mp hi₁).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmem ↦ hnot ?_⟩
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      exact (mem_retainedDomain parent τ Acc i).mpr ⟨hi₂, j, hj⟩
    · intro _ _ _
      exact Nat.zero_le _
  have hsplit : ∑ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter
        (fun i ↦ parent i ∈ Acc), Fintype.card (E.model i) +
      ∑ i ∈ (Finset.univ \ retainedDomain parent τ Acc).filter (fun i ↦ ¬ parent i ∈ Acc),
        Fintype.card (E.model i) =
      ∑ i ∈ Finset.univ \ retainedDomain parent τ Acc, Fintype.card (E.model i) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  omega

end RetainedMatching
end GroupApproximation
