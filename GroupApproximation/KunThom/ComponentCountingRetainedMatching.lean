import GroupApproximation.KunThom.FixedPointNormalizationPatching
import GroupApproximation.Criterion.Criterion
import Mathlib.Order.SymmDiff

/-!
# Transferring the component matching to retained objects

The quantitative component matching of Kun–Thom (arXiv:2608.06222, proof of
Lemma 4.3) is proved for whole `Γ`-blocks: an acceptable block `B` and its
dominant target `B'` satisfy `|u B △ B'| ≤ δ |B|`.  The cluster objects are
retained subsets of those blocks.  Deleting the removed parts costs at most the
removed mass of the two blocks.

* `card_image_symmDiff_le`: for `Q ⊆ B` and `Q' ⊆ B'`,
  `|u Q △ Q'| ≤ |u B △ B'| + |B \ Q| + |B' \ Q'|`.
* `card_retained_symmDiff_le`: the same bound with removed masses written as
  differences of cardinalities.
* `BlockEmbedding.objectImage` and `card_objectImage`: the ambient image of a
  retained object.
* `IsRetainedMatch` and `retainedMatch_unique_target`, `retainedMatch_unique_source`:
  the object-level matching induced by an injective parent map, and its
  injectivity on objects with acceptable parents.
-/

namespace GroupApproximation
namespace RetainedMatching

open scoped symmDiff

universe u

variable {Y : FiniteModel}

/-- **Retained symmetric difference.**  Shrinking a block and its target to
subsets changes the symmetric difference of the translate by at most the two
removed masses. -/
theorem card_image_symmDiff_le (q : Equiv.Perm Y) {Q B Q' B' : Finset Y}
    (hQ : Q ⊆ B) (hQ' : Q' ⊆ B') :
    ((Q.image q) ∆ Q').card ≤ ((B.image q) ∆ B').card + (B \ Q).card + (B' \ Q').card := by
  have hsub : (Q.image q) ∆ Q' ⊆ ((B.image q) ∆ B' ∪ (B \ Q).image q) ∪ (B' \ Q') := by
    intro y hy
    rcases Finset.mem_symmDiff.mp hy with ⟨hyQ, hyQ'⟩ | ⟨hyQ', hyQ⟩
    · by_cases hyB' : y ∈ B'
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hyB', hyQ'⟩)
      · refine Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_symmDiff.mpr (Or.inl ⟨?_, hyB'⟩)))
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyQ
        exact Finset.mem_image_of_mem q (hQ hx)
    · by_cases hyB : y ∈ B.image q
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyB
        exact Finset.mem_image_of_mem q
          (Finset.mem_sdiff.mpr ⟨hx, fun hxQ ↦ hyQ (Finset.mem_image_of_mem q hxQ)⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_symmDiff.mpr (Or.inr ⟨hQ' hyQ', hyB⟩)))
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le ((B.image q) ∆ B' ∪ (B \ Q).image q) (B' \ Q')
  have h₃ := Finset.card_union_le ((B.image q) ∆ B') ((B \ Q).image q)
  have h₄ : ((B \ Q).image q).card = (B \ Q).card :=
    Finset.card_image_of_injective _ q.injective
  omega

/-- The retained symmetric-difference bound with the removed masses written as
differences of cardinalities. -/
theorem card_retained_symmDiff_le (q : Equiv.Perm Y) {Q B Q' B' : Finset Y}
    (hQ : Q ⊆ B) (hQ' : Q' ⊆ B') :
    (((Q.image q) ∆ Q').card : ℝ) ≤
      ((B.image q) ∆ B').card + ((B.card : ℝ) - Q.card) + ((B'.card : ℝ) - Q'.card) := by
  have h := card_image_symmDiff_le q hQ hQ'
  have hB := Finset.card_sdiff_add_card_eq_card hQ
  have hB' := Finset.card_sdiff_add_card_eq_card hQ'
  have hcast : (((Q.image q) ∆ Q').card : ℝ) ≤
      (((B.image q) ∆ B').card : ℝ) + ((B \ Q).card : ℝ) + ((B' \ Q').card : ℝ) := by
    exact_mod_cast h
  have hBr : ((B \ Q).card : ℝ) = (B.card : ℝ) - Q.card := by
    have : ((B \ Q).card : ℝ) + Q.card = B.card := by exact_mod_cast hB
    linarith
  have hB'r : ((B' \ Q').card : ℝ) = (B'.card : ℝ) - Q'.card := by
    have : ((B' \ Q').card : ℝ) + Q'.card = B'.card := by exact_mod_cast hB'
    linarith
  rw [hBr, hB'r] at hcast
  exact hcast

end RetainedMatching

namespace BlockPatching
namespace BlockEmbedding

universe u

variable {Y : FiniteModel} {I : Type u}

/-- The ambient image of a retained object. -/
noncomputable def objectImage (E : BlockEmbedding Y I) (i : I) : Finset Y :=
  Finset.univ.image (E.embed i)

theorem mem_objectImage (E : BlockEmbedding Y I) (i : I) (x : E.model i) :
    E.embed i x ∈ E.objectImage i :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- A retained object has as many ambient points as it has points. -/
theorem card_objectImage (E : BlockEmbedding Y I) (i : I) :
    (E.objectImage i).card = Fintype.card (E.model i) := by
  rw [objectImage, Finset.card_image_of_injective _ (E.embed_injective i), Finset.card_univ]

end BlockEmbedding
end BlockPatching

namespace RetainedMatching

universe u

variable {Y : FiniteModel} {I : Type u} {J : Type*}

/-- Object `j` is the retained match of object `i` when the parent block of `j` is
the dominant target of the parent block of `i`. -/
def IsRetainedMatch (parent : I → J) (τ : J → J) (i j : I) : Prop :=
  parent j = τ (parent i)

/-- An injective parent map makes the retained match of an object unique. -/
theorem retainedMatch_unique_target {parent : I → J} (hparent : Function.Injective parent)
    {τ : J → J} {i j j' : I} (h : IsRetainedMatch parent τ i j)
    (h' : IsRetainedMatch parent τ i j') : j = j' :=
  hparent (h.trans h'.symm)

/-- On objects whose parents lie where the dominant target is injective, the
retained matching is injective. -/
theorem retainedMatch_unique_source {parent : I → J} (hparent : Function.Injective parent)
    {τ : J → J} {Acc : Set J} (hτ : Set.InjOn τ Acc) {i i' j : I}
    (hi : parent i ∈ Acc) (hi' : parent i' ∈ Acc)
    (h : IsRetainedMatch parent τ i j) (h' : IsRetainedMatch parent τ i' j) : i = i' :=
  hparent (hτ hi hi' (h.symm.trans h'))

end RetainedMatching
end GroupApproximation
