import GroupApproximation.KunThom.StepNineHammingReference
import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBlockWords

/-!
# Step 9: equivariance defects of transported arrows

The per-block estimate of step 9 in Kun and Thom's proof of Theorem 4.1
(arXiv:2608.06222v3) re-separates an arrow `a_i` of the bisection `â` from the
transported arrow of `b_{π i}` at a scale proportional to their actual
equivariance defects.  This file bounds the defect of a transported arrow by
quantities that sum over disjoint blocks.

* `BlockAction.wordAction A ws`: the labelled action in which the label `s` acts
  through the word `ws s`.
* `BlockEmbedding.bridgeLabelFailure E q A A' C s`: the points of block `C` at
  which `q` fails to conjugate the ambient action of `s` in `A` into that in `A'`.
* `BlockEmbedding.card_equivarianceDefect_bridge_le_local`: the bridge defect
  bound of `ComponentCountingRelativeFunctorBridges` with the conjugation failures
  counted on the source block only.
* `BlockEmbedding.card_equivarianceDefect_transportArrow_le`: the defect of a
  transported arrow is at most the two localized bridge defects plus
  `|L| · (sourceDefect + k · #defect)` of the arrow, for words of length `≤ k`.
* `BlockEmbedding.sum_card_bridgeLabelFailure_le`: the localized failures of all
  blocks sum to at most the ambient failures.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

namespace BlockAction

variable {E : BlockEmbedding Y I}

/-- The labelled action in which the label `s` acts through the word `ws s`. -/
def wordAction {L : Type*} (A : BlockAction E L) (ws : L → List L) : BlockAction E L where
  act s := wordAct A.act (ws s)
  blockAct C s := wordAct (A.blockAct C) (ws s)

/-- The compatibility failures of the word action are those of the words. -/
theorem wordAction_compatFailure {L : Type*} (A : BlockAction E L) (ws : L → List L)
    (C : I) (s : L) :
    (A.wordAction ws).compatFailure C s = A.wordCompatFailure C (ws s) :=
  rfl

end BlockAction

namespace BlockEmbedding

/-- The points of block `C` at which `q` fails to conjugate the ambient action of the
label `s` in `A` into its ambient action in `A'`. -/
noncomputable def bridgeLabelFailure {L : Type*} (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (A A' : BlockAction E L) (C : I) (s : L) : Finset (E.model C) :=
  Finset.univ.filter fun x ↦ q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))

/-- **One label, localized.**  The defect of the bridge at label `s` is at most its
missing source mass, the compatibility failures of both block actions at `s`, and
the points of the source block at which `q` fails to conjugate `A.act s` into
`A'.act s`. -/
theorem card_bridge_labelSlice_le_local {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) (A A' : BlockAction E L)
    (s : L) :
    (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ (E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)).card ≤
      (E.bridge q C D).sourceDefect + (A.compatFailure C s).card +
        (E.bridgeLabelFailure q A A' C s).card + (A'.compatFailure D s).card := by
  have hsub : (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ (E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)) ⊆
      ((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s) ∪
        (Finset.univ.filter fun x : E.model C ↦
          q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))) ∪
        (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D)) := by
    intro x hx
    by_cases h₀ : x ∈ (E.bridge q C D).source
    swap
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h₀⟩)))
    by_cases h₁ : x ∈ A.compatFailure C s
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₁))
    by_cases h₂ : q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩))
    by_cases h₃ : q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₃⟩)
    exfalso
    push Not at h₂
    have hdef := (Finset.mem_filter.mp hx).2
    rw [mem_equivarianceDefect] at hdef
    dsimp only at hdef
    have hz := E.embed_bridge_apply q C D x h₀
    have hcompatC := A.embed_blockAct_of_not_mem h₁
    have hnotD : (E.bridge q C D).apply x h₀ ∉ A'.compatFailure D s := by
      intro hmem
      apply h₃
      rw [← hz]
      exact Finset.mem_image_of_mem _ hmem
    have hcompatD := A'.embed_blockAct_of_not_mem hnotD
    have hkey : E.embed D (A'.blockAct D s ((E.bridge q C D).apply x h₀)) =
        q (E.embed C (A.blockAct C s x)) := by
      rw [hcompatD, hz, hcompatC, h₂]
    have hsrc : A.blockAct C s x ∈ (E.bridge q C D).source :=
      (E.mem_bridgeSource q C D _).mpr ⟨_, hkey⟩
    apply hdef h₀ hsrc
    apply E.embed_injective D
    rw [E.embed_bridge_apply q C D _ hsrc, hkey]
  have hcard := Finset.card_le_card hsub
  have hu₁ := Finset.card_union_le
    (((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s) ∪
      (Finset.univ.filter fun x : E.model C ↦
        q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))))
    (Finset.univ.filter fun x : E.model C ↦
      q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D))
  have hu₂ := Finset.card_union_le
    ((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s)
    (Finset.univ.filter fun x : E.model C ↦
      q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x)))
  have hu₃ := Finset.card_union_le (Finset.univ \ (E.bridge q C D).source)
    (A.compatFailure C s)
  have hsd : (Finset.univ \ (E.bridge q C D).source).card ≤ (E.bridge q C D).sourceDefect := by
    have hsplit := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (E.bridge q C D).source)
    rw [Finset.card_univ] at hsplit
    unfold FinitePartialBijection.sourceDefect
    omega
  have hlocal : (Finset.univ.filter fun x : E.model C ↦
        q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))).card =
      (E.bridgeLabelFailure q A A' C s).card :=
    rfl
  have hpull : (Finset.univ.filter fun x : E.model C ↦
        q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D)).card ≤
      (A'.compatFailure D s).card := by
    refine le_trans ?_ (Finset.card_image_le (s := A'.compatFailure D s) (f := E.embed D))
    apply Finset.card_le_card_of_injOn (fun x ↦ q (E.embed C x))
    · intro x hx
      rw [Finset.mem_coe] at hx ⊢
      exact (Finset.mem_filter.mp hx).2
    · intro x _ x' _ hxx'
      exact E.embed_injective C (q.injective hxx')
  omega

/-- **Localized bridge defect.**  The equivariance defect of a bridge is at most,
summed over labels, its missing source mass, the compatibility failures of both
block actions, and the conjugation failures of `q` on the source block. -/
theorem card_equivarianceDefect_bridge_le_local {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) (A A' : BlockAction E L) :
    ((E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)).card ≤
      ∑ s : L, ((E.bridge q C D).sourceDefect + (A.compatFailure C s).card +
        (E.bridgeLabelFailure q A A' C s).card + (A'.compatFailure D s).card) :=
  (card_le_sum_labelSlices _).trans
    (Finset.sum_le_sum fun s _ ↦ card_bridge_labelSlice_le_local E q C D A A' s)

/-- **Defect of a transported arrow.**  The arrow of block `C` of `β`, transported
from block `C'` into block `D`, is almost equivariant for the labels of `A` on
both ends.  Its defect is at most the localized defect of the bridge realized by
`q` from `C'`, with the word labels `ws` on `C`, the defect of the arrow for the
word labels, and the localized defect of the bridge realized by `q⁻¹` into `D`. -/
theorem card_equivarianceDefect_transportArrow_le {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (β : BlockArrows E) (C C' D : I)
    (A : BlockAction E L) (ws : L → List L) {k : ℕ} (hk : ∀ s, (ws s).length ≤ k) :
    ((E.transportArrow q β C C' D).equivarianceDefect (A.blockAct C') (A.blockAct D)).card ≤
      ∑ s : L, ((E.bridge q C' C).sourceDefect + (A.compatFailure C' s).card +
          (E.bridgeLabelFailure q A (A.wordAction ws) C' s).card +
          ((A.wordAction ws).compatFailure C s).card) +
        Fintype.card L * ((β.arrow C).sourceDefect +
          k * ((β.arrow C).equivarianceDefect (A.blockAct C)
            (A.blockAct (β.objEquiv C))).card) +
        ∑ s : L, ((E.bridge q⁻¹ (β.objEquiv C) D).sourceDefect +
          ((A.wordAction ws).compatFailure (β.objEquiv C) s).card +
          (E.bridgeLabelFailure q⁻¹ (A.wordAction ws) A (β.objEquiv C) s).card +
          (A.compatFailure D s).card) := by
  have h₁ : ((E.transportArrow q β C C' D).equivarianceDefect (A.blockAct C')
        (A.blockAct D)).card ≤
      (((E.bridge q C' C).trans (β.arrow C)).equivarianceDefect (A.blockAct C')
        ((A.wordAction ws).blockAct (β.objEquiv C))).card +
        ((E.bridge q⁻¹ (β.objEquiv C) D).equivarianceDefect
          ((A.wordAction ws).blockAct (β.objEquiv C)) (A.blockAct D)).card :=
    card_equivarianceDefect_trans_le (A.blockAct C')
      ((A.wordAction ws).blockAct (β.objEquiv C)) (A.blockAct D)
      ((E.bridge q C' C).trans (β.arrow C)) (E.bridge q⁻¹ (β.objEquiv C) D)
  have h₂ := card_equivarianceDefect_trans_le (A.blockAct C')
    ((A.wordAction ws).blockAct C) ((A.wordAction ws).blockAct (β.objEquiv C))
    (E.bridge q C' C) (β.arrow C)
  have h₃ := E.card_equivarianceDefect_bridge_le_local q C' C A (A.wordAction ws)
  have h₄ := E.card_equivarianceDefect_bridge_le_local q⁻¹ (β.objEquiv C) D
    (A.wordAction ws) A
  have h₅ : ((β.arrow C).equivarianceDefect ((A.wordAction ws).blockAct C)
        ((A.wordAction ws).blockAct (β.objEquiv C))).card ≤
      Fintype.card L * ((β.arrow C).sourceDefect +
        k * ((β.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (β.objEquiv C))).card) :=
    card_equivarianceDefect_wordAct_le (β.arrow C) (A.blockAct C)
      (A.blockAct (β.objEquiv C)) ws hk
  omega

/-- Block filters of an ambient predicate sum to at most the ambient filter, since
the blocks are disjoint. -/
theorem sum_card_filter_embed_le [Fintype I] (E : BlockEmbedding Y I) (P : Y → Prop)
    [DecidablePred P] :
    ∑ C, (Finset.univ.filter fun x : E.model C ↦ P (E.embed C x)).card ≤
      (Finset.univ.filter P).card := by
  have hsigma : (Finset.univ.sigma fun C ↦
        Finset.univ.filter fun x : E.model C ↦ P (E.embed C x)).card =
      ∑ C, (Finset.univ.filter fun x : E.model C ↦ P (E.embed C x)).card :=
    Finset.card_sigma _ _
  rw [← hsigma]
  refine Finset.card_le_card_of_injOn (fun p ↦ E.embed p.1 p.2) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe] at hp ⊢
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2⟩
  · rintro ⟨C, x⟩ - ⟨C', z⟩ - h
    have hCC : C = C' := E.embed_disjoint C C' x z h
    subst hCC
    have hxz : x = z := E.embed_injective C h
    subst hxz
    rfl

/-- **Localized label failures sum to the ambient ones.** -/
theorem sum_card_bridgeLabelFailure_le [Fintype I] {L : Type*} (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (A A' : BlockAction E L) (s : L) :
    ∑ C, (E.bridgeLabelFailure q A A' C s).card ≤
      (Finset.univ.filter fun y : Y ↦ q (A.act s y) ≠ A'.act s (q y)).card :=
  E.sum_card_filter_embed_le fun y ↦ q (A.act s y) ≠ A'.act s (q y)

end BlockEmbedding

end BlockPatching
end GroupApproximation
