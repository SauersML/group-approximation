import GroupApproximation.KunThom.ComponentCountingRelativeFunctorWords
import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBridges

/-!
# Word actions on embedded blocks

In the proof of Kun–Thom Lemma 4.3 (arXiv:2608.06222), a compressor `t`
conjugates a generator `s` of `Γ` to an element `t s t⁻¹` of `Γ`.  That element
has its own completed action on each component, while an allowed arrow is only
controlled for the generator labels.  Its action is therefore compared with the
action of a word `w_s` in the generators.  This file counts the two sources of
disagreement on one block.

* `wordCompatFailure A C w`: the block points where the block action of the word
  `w` differs from its ambient action.  `card_wordCompatFailure_le` bounds its
  size by the compatibility failures of the letters.
* `card_labelDisagreement_blockWords_le`: the completed action of a label and
  the block action of its word differ at most where the label is not compatible,
  where the ambient label and the ambient word disagree, and where the word is
  not compatible.
-/

namespace GroupApproximation
namespace BlockPatching
namespace BlockAction

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u} {E : BlockEmbedding Y I}

/-- The block points where the block action of a word differs from its ambient
action. -/
noncomputable def wordCompatFailure {L : Type*} (A : BlockAction E L) (C : I) (w : List L) :
    Finset (E.model C) := by
  classical
  exact Finset.univ.filter fun x ↦
    E.embed C (wordAct (A.blockAct C) w x) ≠ wordAct A.act w (E.embed C x)

theorem mem_wordCompatFailure {L : Type*} (A : BlockAction E L) (C : I) (w : List L)
    (x : E.model C) :
    x ∈ A.wordCompatFailure C w ↔
      E.embed C (wordAct (A.blockAct C) w x) ≠ wordAct A.act w (E.embed C x) := by
  classical
  simp [wordCompatFailure]

/-- A compatibility failure of `l :: w` is a failure of `w`, or a failure of the
letter `l` at the image of the point under `w`. -/
theorem wordCompatFailure_cons_subset {L : Type*} (A : BlockAction E L) (C : I) (l : L)
    (w : List L) :
    A.wordCompatFailure C (l :: w) ⊆
      A.wordCompatFailure C w ∪
        (Finset.univ.filter fun x ↦ wordAct (A.blockAct C) w x ∈ A.compatFailure C l) := by
  intro x hx
  by_cases h₁ : x ∈ A.wordCompatFailure C w
  · exact Finset.mem_union_left _ h₁
  by_cases h₂ : wordAct (A.blockAct C) w x ∈ A.compatFailure C l
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩)
  exfalso
  have hw : E.embed C (wordAct (A.blockAct C) w x) = wordAct A.act w (E.embed C x) := by
    by_contra hne
    exact h₁ ((A.mem_wordCompatFailure C w x).mpr hne)
  have hl := A.embed_blockAct_of_not_mem h₂
  apply (A.mem_wordCompatFailure C (l :: w) x).mp hx
  calc E.embed C (wordAct (A.blockAct C) (l :: w) x)
      = E.embed C (A.blockAct C l (wordAct (A.blockAct C) w x)) := rfl
    _ = A.act l (E.embed C (wordAct (A.blockAct C) w x)) := hl
    _ = A.act l (wordAct A.act w (E.embed C x)) := by rw [hw]
    _ = wordAct A.act (l :: w) (E.embed C x) := rfl

/-- **Word compatibility.**  The block action of a word differs from its ambient
action on at most the sum, over its letters, of their compatibility failures. -/
theorem card_wordCompatFailure_le {L : Type*} (A : BlockAction E L) (C : I) (w : List L) :
    (A.wordCompatFailure C w).card ≤ (w.map fun l ↦ (A.compatFailure C l).card).sum := by
  induction w with
  | nil =>
    have hempty : A.wordCompatFailure C [] = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      exact (A.mem_wordCompatFailure C [] x).mp hx rfl
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  | cons l w ih =>
    have hsub := Finset.card_le_card (A.wordCompatFailure_cons_subset C l w)
    have hu := Finset.card_union_le (A.wordCompatFailure C w)
      (Finset.univ.filter fun x ↦ wordAct (A.blockAct C) w x ∈ A.compatFailure C l)
    have hl : (Finset.univ.filter fun x ↦
        wordAct (A.blockAct C) w x ∈ A.compatFailure C l).card ≤ (A.compatFailure C l).card := by
      apply Finset.card_le_card_of_injOn (fun x ↦ wordAct (A.blockAct C) w x)
      · intro x hx
        rw [Finset.mem_coe] at hx ⊢
        exact (Finset.mem_filter.mp hx).2
      · intro x _ x' _ hxx'
        exact (wordAct (A.blockAct C) w).injective hxx'
    rw [List.map_cons, List.sum_cons]
    omega

/-- **Completed labels against block words.**  For a family of words `ws`, the
completed action of a label and the block action of its word differ at most
where the label fails to be compatible, where the ambient label and the ambient
word disagree, and where the word fails to be compatible. -/
theorem card_labelDisagreement_blockWords_le {L L' : Type*} [Fintype L'] [DecidableEq L']
    (A : BlockAction E L) (A' : BlockAction E L') (C : I) (ws : L' → List L) :
    (labelDisagreement (A'.blockAct C) fun s ↦ wordAct (A.blockAct C) (ws s)).card ≤
      ∑ s : L', ((A'.compatFailure C s).card +
        (Finset.univ.filter fun y : Y ↦ A'.act s y ≠ wordAct A.act (ws s) y).card +
          (A.wordCompatFailure C (ws s)).card) := by
  refine (BlockEmbedding.card_le_sum_labelSlices _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
  have hsub : (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ labelDisagreement (A'.blockAct C) fun s ↦ wordAct (A.blockAct C) (ws s)) ⊆
      (A'.compatFailure C s ∪
        (Finset.univ.filter fun x : E.model C ↦
          A'.act s (E.embed C x) ≠ wordAct A.act (ws s) (E.embed C x))) ∪
        A.wordCompatFailure C (ws s) := by
    intro x hx
    by_cases h₁ : x ∈ A'.compatFailure C s
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h₁)
    by_cases h₂ : A'.act s (E.embed C x) ≠ wordAct A.act (ws s) (E.embed C x)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩))
    by_cases h₃ : x ∈ A.wordCompatFailure C (ws s)
    · exact Finset.mem_union_right _ h₃
    exfalso
    push Not at h₂
    have hdis := (mem_labelDisagreement _ _ (s, x)).mp (Finset.mem_filter.mp hx).2
    have hw : E.embed C (wordAct (A.blockAct C) (ws s) x) =
        wordAct A.act (ws s) (E.embed C x) := by
      by_contra hne
      exact h₃ ((A.mem_wordCompatFailure C (ws s) x).mpr hne)
    apply hdis
    apply E.embed_injective C
    show E.embed C (A'.blockAct C s x) = E.embed C (wordAct (A.blockAct C) (ws s) x)
    rw [A'.embed_blockAct_of_not_mem h₁, h₂, hw]
  have hcard := Finset.card_le_card hsub
  have hu₁ := Finset.card_union_le (A'.compatFailure C s ∪
    (Finset.univ.filter fun x : E.model C ↦
      A'.act s (E.embed C x) ≠ wordAct A.act (ws s) (E.embed C x)))
    (A.wordCompatFailure C (ws s))
  have hu₂ := Finset.card_union_le (A'.compatFailure C s)
    (Finset.univ.filter fun x : E.model C ↦
      A'.act s (E.embed C x) ≠ wordAct A.act (ws s) (E.embed C x))
  have hamb : (Finset.univ.filter fun x : E.model C ↦
        A'.act s (E.embed C x) ≠ wordAct A.act (ws s) (E.embed C x)).card ≤
      (Finset.univ.filter fun y : Y ↦ A'.act s y ≠ wordAct A.act (ws s) y).card := by
    apply Finset.card_le_card_of_injOn (E.embed C)
    · intro x hx
      rw [Finset.mem_coe] at hx ⊢
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · intro x _ x' _ hxx'
      exact E.embed_injective C hxx'
  omega

end BlockAction
end BlockPatching
end GroupApproximation
