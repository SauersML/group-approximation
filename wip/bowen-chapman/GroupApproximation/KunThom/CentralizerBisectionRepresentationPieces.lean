import GroupApproximation.KunThom.CentralizerBisectionRepresentationDefects
import GroupApproximation.KunThom.BisectionActualDefect

/-!
# The pieces of a block under an almost-centralizer

A permutation `q` of the ambient model cuts a block `C` into pieces: the sources of
the bridges `E.bridge q C D` into the blocks `D`, and the points sent off every
block (`BlockEmbedding.offBlocks`).  If `q` almost commutes with the labels, every
piece is almost invariant under the block action of `C`.  With exact tagged
expansion, every piece of at most half of `C` is then small, so `C` is covered by
its dominant piece, its off-block points and the boundary of the other pieces.
This is the finite input for the mass of the blocks that carry no candidate
bridge, in the forward half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4).

* `BlockAction.enteringFailure A s`: the ambient points that the label `s`
  carries onto the image of a compatibility failure.  A boundary arc entering a
  piece away from the local obstructions starts at such a point
  (`mem_enteringFailure_of_enter`), and these points number at most the
  compatibility failures (`card_enteringFailure_le`).
* `sum_card_taggedBoundary_bridgeSource_le`: summed over the pieces, the boundary
  of the pieces of `C` is at most twice the local obstructions of `q` on `C` plus
  the points of `C` sent to entering failures.
* `card_model_le_sum_bridgeSource_add_offBlocks`: the pieces cover the block.
* `mul_card_model_le_dominant` and `mul_card_model_le_of_no_majority`: with tagged
  expansion at level `c`, `c |C|` is at most `c` times the dominant piece and the
  off-block points plus the boundary of the pieces, and without a majority piece
  the dominant piece drops out.
* `sum_card_offBlocks_le` and `sum_card_filter_enteringFailure_le`: the off-block
  points and the entering points of all blocks sum to at most the uncovered mass
  and the compatibility failures.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

namespace BlockAction

variable {E : BlockEmbedding Y I} {L : Type*}

/-- Ambient points that the label `s` carries onto the image, under the block action of `s`,
of a compatibility failure of some block. -/
noncomputable def enteringFailure [Fintype I] (A : BlockAction E L) (s : L) : Finset Y := by
  classical
  exact (Finset.univ.sigma fun D ↦ A.compatFailure D s).image fun d ↦
    (A.act s).symm (E.embed d.1 (A.blockAct d.1 s d.2))

theorem card_enteringFailure_le [Fintype I] (A : BlockAction E L) (s : L) :
    (A.enteringFailure s).card ≤ ∑ D, (A.compatFailure D s).card := by
  classical
  unfold enteringFailure
  exact Finset.card_image_le.trans (Finset.card_sigma _ _).le

/-- **An entering arc charges an entering failure.**  Let `b` realize `p` on its source and
contain every point of block `C` that `p` carries into block `C'`.  If the label `s` carries
a point `x` outside the source into the source, and `x` carries no local obstruction, then
`p` sends `x` to an entering failure. -/
theorem mem_enteringFailure_of_enter [Fintype I] (A : BlockAction E L) (p : Equiv.Perm Y)
    {C C' : I} (b : FinitePartialBijection (E.model C) (E.model C'))
    (hreal : ∀ x (hx : x ∈ b.source), E.embed C' (b.apply x hx) = p (E.embed C x))
    (hmax : ∀ x (z : E.model C'), E.embed C' z = p (E.embed C x) → x ∈ b.source)
    {s : L} {x : E.model C} (hout : x ∉ b.source) (hin : A.blockAct C s x ∈ b.source)
    (hLO : x ∉ A.localObstruction p C s) : p (E.embed C x) ∈ A.enteringFailure s := by
  classical
  have hcomm : p (A.act s (E.embed C x)) = A.act s (p (E.embed C x)) := by
    by_contra hne
    exact hLO ((A.mem_localObstruction p C s x).mpr
      (Or.inl ((A.mem_commutationFailure p s _).mpr hne)))
  have hcompatC : x ∉ A.compatFailure C s := fun hmem ↦
    hLO ((A.mem_localObstruction p C s x).mpr (Or.inr (Or.inl hmem)))
  have hamb : E.embed C' (b.apply _ hin) = A.act s (p (E.embed C x)) := by
    rw [hreal _ hin, A.embed_blockAct_of_not_mem hcompatC, hcomm]
  have hw : (A.blockAct C' s).symm (b.apply _ hin) ∈ A.compatFailure C' s := by
    by_contra hw
    have hcw := A.embed_blockAct_of_not_mem hw
    rw [Equiv.apply_symm_apply, hamb] at hcw
    exact hout (hmax x _ ((A.act s).injective hcw).symm)
  unfold enteringFailure
  refine Finset.mem_image.mpr ⟨⟨C', (A.blockAct C' s).symm (b.apply _ hin)⟩,
    Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hw⟩, ?_⟩
  show (A.act s).symm (E.embed C' (A.blockAct C' s
    ((A.blockAct C' s).symm (b.apply _ hin)))) = p (E.embed C x)
  rw [Equiv.apply_symm_apply, hamb, Equiv.symm_apply_apply]

end BlockAction

namespace BlockEmbedding

/-- The points of block `C` that `q` sends off every block. -/
noncomputable def offBlocks (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C : I) :
    Finset (E.model C) :=
  Finset.univ.filter fun x ↦ q (E.embed C x) ∈ E.uncovered

theorem mem_offBlocks (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C : I) (x : E.model C) :
    x ∈ E.offBlocks q C ↔ q (E.embed C x) ∈ E.uncovered := by
  simp [offBlocks]

/-- **The pieces cover the block.** -/
theorem card_model_le_sum_bridgeSource_add_offBlocks [Fintype I] (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (C : I) :
    Fintype.card (E.model C) ≤
      ∑ D, (E.bridge q C D).source.card + (E.offBlocks q C).card := by
  classical
  have hsub : (Finset.univ : Finset (E.model C)) ⊆
      (Finset.univ.biUnion fun D ↦ (E.bridge q C D).source) ∪ E.offBlocks q C := by
    intro x _
    by_cases hx : ∃ (D : I) (z : E.model D), E.embed D z = q (E.embed C x)
    · obtain ⟨D, z, hz⟩ := hx
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨D, Finset.mem_univ _, (E.mem_bridgeSource q C D x).mpr ⟨z, hz⟩⟩)
    · refine Finset.mem_union_right _ ((E.mem_offBlocks q C x).mpr (E.mem_uncovered.mpr ?_))
      intro D z hz
      exact hx ⟨D, z, hz⟩
  calc Fintype.card (E.model C) = (Finset.univ : Finset (E.model C)).card :=
        Finset.card_univ.symm
    _ ≤ ((Finset.univ.biUnion fun D ↦ (E.bridge q C D).source) ∪ E.offBlocks q C).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.biUnion fun D ↦ (E.bridge q C D).source).card +
          (E.offBlocks q C).card :=
        Finset.card_union_le _ _
    _ ≤ ∑ D, (E.bridge q C D).source.card + (E.offBlocks q C).card :=
        Nat.add_le_add_right Finset.card_biUnion_le _

/-- The off-block points of all blocks number at most the uncovered mass. -/
theorem sum_card_offBlocks_le [Fintype I] (E : BlockEmbedding Y I) (q : Equiv.Perm Y) :
    ∑ C, (E.offBlocks q C).card ≤ E.uncovered.card :=
  E.sum_card_filter_perm_embed_mem_le q E.uncovered

/-- The pieces of a block meet a set in at most its size. -/
theorem sum_card_bridgeSource_inter_le [Fintype I] (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (C : I) (K : Finset (E.model C)) :
    ∑ D, ((E.bridge q C D).source ∩ K).card ≤ K.card := by
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun D _ ↦ Finset.inter_subset_right)
  · intro D _ D' _ hne
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (E.disjoint_bridge_source q C hne))

/-- The preimages of the pieces under a permutation of the block meet a set in at most its
size. -/
theorem sum_card_filter_perm_mem_bridgeSource_inter_le [Fintype I] (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (C : I) (σ : Equiv.Perm (E.model C)) (K : Finset (E.model C)) :
    ∑ D, ((Finset.univ.filter fun x ↦ σ x ∈ (E.bridge q C D).source) ∩ K).card ≤ K.card := by
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun D _ ↦ Finset.inter_subset_right)
  · intro D _ D' _ hne
    refine Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left ?_)
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.mp (E.disjoint_bridge_source q C hne)
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx').2

/-- A block has a dominant piece. -/
theorem exists_dominant_bridge [Fintype I] (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (C : I) : ∃ D₀, ∀ D, (E.bridge q C D).source.card ≤ (E.bridge q C D₀).source.card := by
  obtain ⟨D₀, _, hD₀⟩ := Finset.exists_max_image (Finset.univ : Finset I)
    (fun D ↦ (E.bridge q C D).source.card) ⟨C, Finset.mem_univ _⟩
  exact ⟨D₀, fun D ↦ hD₀ D (Finset.mem_univ _)⟩

/-- A piece other than the dominant piece has at most half of the block. -/
theorem two_mul_card_bridgeSource_le_of_ne (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (C : I) {D₀ D : I}
    (hD₀ : ∀ D, (E.bridge q C D).source.card ≤ (E.bridge q C D₀).source.card)
    (hne : D ≠ D₀) : 2 * (E.bridge q C D).source.card ≤ Fintype.card (E.model C) := by
  have hunion := Finset.card_union_of_disjoint (E.disjoint_bridge_source q C hne)
  have hle : ((E.bridge q C D).source ∪ (E.bridge q C D₀).source).card ≤
      Fintype.card (E.model C) := Finset.card_le_univ _
  have hmax := hD₀ D
  omega

end BlockEmbedding

namespace BlockAction

variable {E : BlockEmbedding Y I} {L : Type*}

/-- **Boundary slices of the pieces.**  At the label `s`, the boundary of all the pieces of
block `C` is at most twice its local obstructions plus its points sent to entering
failures. -/
theorem sum_card_boundarySlice_le [Fintype I] [DecidableEq L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) (s : L) :
    ∑ D, (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ taggedBoundary (A.blockAct C) (E.bridge q C D).source).card ≤
      2 * (A.localObstruction q C s).card +
        (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ A.enteringFailure s).card := by
  classical
  have hslice : ∀ D, (Finset.univ.filter fun x : E.model C ↦
      (s, x) ∈ taggedBoundary (A.blockAct C) (E.bridge q C D).source).card ≤
      ((E.bridge q C D).source ∩ A.localObstruction q C s).card +
        ((Finset.univ.filter fun x ↦ A.blockAct C s x ∈ (E.bridge q C D).source) ∩
          (A.localObstruction q C s ∪ Finset.univ.filter fun x : E.model C ↦
            q (E.embed C x) ∈ A.enteringFailure s)).card := by
    intro D
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro x hx
    have hbd := (Finset.mem_filter.mp hx).2
    rw [mem_taggedBoundary] at hbd
    dsimp only at hbd
    rcases hbd with ⟨hin, hout⟩ | ⟨hout, hin⟩
    · refine Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hin, ?_⟩)
      by_contra hLO
      exact hout ((E.mem_bridgeSource q C D _).mpr
        ⟨_, A.embed_blockAct_apply_eq q (E.bridge q C D) (E.embed_bridge_apply q C D) hin hLO⟩)
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩, ?_⟩)
      by_cases hLO : x ∈ A.localObstruction q C s
      · exact Finset.mem_union_left _ hLO
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          A.mem_enteringFailure_of_enter q (E.bridge q C D) (E.embed_bridge_apply q C D)
            (fun y z hz ↦ (E.mem_bridgeSource q C D y).mpr ⟨z, hz⟩) hout hin hLO⟩)
  have h₁ := E.sum_card_bridgeSource_inter_le q C (A.localObstruction q C s)
  have h₂ := E.sum_card_filter_perm_mem_bridgeSource_inter_le q C (A.blockAct C s)
    (A.localObstruction q C s ∪ Finset.univ.filter fun x : E.model C ↦
      q (E.embed C x) ∈ A.enteringFailure s)
  have h₃ := Finset.card_union_le (A.localObstruction q C s)
    (Finset.univ.filter fun x : E.model C ↦ q (E.embed C x) ∈ A.enteringFailure s)
  have h₄ : ∑ D, (Finset.univ.filter fun x : E.model C ↦
      (s, x) ∈ taggedBoundary (A.blockAct C) (E.bridge q C D).source).card ≤
      ∑ D, (((E.bridge q C D).source ∩ A.localObstruction q C s).card +
        ((Finset.univ.filter fun x ↦ A.blockAct C s x ∈ (E.bridge q C D).source) ∩
          (A.localObstruction q C s ∪ Finset.univ.filter fun x : E.model C ↦
            q (E.embed C x) ∈ A.enteringFailure s)).card) :=
    Finset.sum_le_sum fun D _ ↦ hslice D
  rw [Finset.sum_add_distrib] at h₄
  omega

/-- **The boundary of the pieces.**  Summed over the pieces and the labels, the boundary of
the pieces of block `C` is at most twice its local obstructions plus its points sent to
entering failures. -/
theorem sum_card_taggedBoundary_bridgeSource_le [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) :
    ∑ D, (taggedBoundary (A.blockAct C) (E.bridge q C D).source).card ≤
      ∑ s : L, (2 * (A.localObstruction q C s).card +
        (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ A.enteringFailure s).card) := by
  classical
  calc ∑ D, (taggedBoundary (A.blockAct C) (E.bridge q C D).source).card
      ≤ ∑ D, ∑ s : L, (Finset.univ.filter fun x : E.model C ↦
          (s, x) ∈ taggedBoundary (A.blockAct C) (E.bridge q C D).source).card :=
        Finset.sum_le_sum fun D _ ↦ BlockEmbedding.card_le_sum_labelSlices _
    _ = ∑ s : L, ∑ D, (Finset.univ.filter fun x : E.model C ↦
          (s, x) ∈ taggedBoundary (A.blockAct C) (E.bridge q C D).source).card :=
        Finset.sum_comm
    _ ≤ ∑ s : L, (2 * (A.localObstruction q C s).card +
          (Finset.univ.filter fun x : E.model C ↦
            q (E.embed C x) ∈ A.enteringFailure s).card) :=
        Finset.sum_le_sum fun s _ ↦ A.sum_card_boundarySlice_le q C s

/-- The points of all blocks sent to entering failures number at most the compatibility
failures. -/
theorem sum_card_filter_enteringFailure_le [Fintype I] (A : BlockAction E L)
    (q : Equiv.Perm Y) (s : L) :
    ∑ C, (Finset.univ.filter fun x : E.model C ↦ q (E.embed C x) ∈ A.enteringFailure s).card ≤
      ∑ D, (A.compatFailure D s).card :=
  (E.sum_card_filter_perm_embed_mem_le q (A.enteringFailure s)).trans
    (A.card_enteringFailure_le s)

/-- Tagged expansion at level `c` bounds the pieces of at most half of the block by their
boundary. -/
theorem mul_sum_card_bridgeSource_le [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) (S : Finset I) {c : ℝ}
    (hexp : HasTaggedExpansionAtScale (A.blockAct C) c 1)
    (hsmall : ∀ D ∈ S, 2 * (E.bridge q C D).source.card ≤ Fintype.card (E.model C)) :
    c * ∑ D ∈ S, ((E.bridge q C D).source.card : ℝ) ≤
      ∑ D ∈ S, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun D hD ↦ ?_
  by_cases h0 : (E.bridge q C D).source.card = 0
  · rw [h0, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  · exact hexp.2 _ (Nat.one_le_iff_ne_zero.mpr h0) (hsmall D hD)

/-- **Mass of a block against its dominant piece.**  With tagged expansion at level
`c ≥ 0`, `c |C|` is at most `c` times the dominant piece and the off-block points, plus the
boundary of the pieces. -/
theorem mul_card_model_le_dominant [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) {c : ℝ} (hc : 0 ≤ c)
    (hexp : HasTaggedExpansionAtScale (A.blockAct C) c 1) {D₀ : I}
    (hD₀ : ∀ D, (E.bridge q C D).source.card ≤ (E.bridge q C D₀).source.card) :
    c * (Fintype.card (E.model C) : ℝ) ≤
      c * ((E.bridge q C D₀).source.card : ℝ) + c * ((E.offBlocks q C).card : ℝ) +
        ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) := by
  classical
  have hcard := E.card_model_le_sum_bridgeSource_add_offBlocks q C
  have herase : (E.bridge q C D₀).source.card +
      ∑ D ∈ Finset.univ.erase D₀, (E.bridge q C D).source.card =
        ∑ D, (E.bridge q C D).source.card :=
    Finset.add_sum_erase _ _ (Finset.mem_univ D₀)
  have hnat : Fintype.card (E.model C) ≤ (E.bridge q C D₀).source.card +
      ∑ D ∈ Finset.univ.erase D₀, (E.bridge q C D).source.card + (E.offBlocks q C).card := by
    omega
  have hreal : (Fintype.card (E.model C) : ℝ) ≤ ((E.bridge q C D₀).source.card : ℝ) +
      ∑ D ∈ Finset.univ.erase D₀, ((E.bridge q C D).source.card : ℝ) +
        ((E.offBlocks q C).card : ℝ) := by
    exact_mod_cast hnat
  have hexpand := A.mul_sum_card_bridgeSource_le q C (Finset.univ.erase D₀) hexp
    (fun D hD ↦ E.two_mul_card_bridgeSource_le_of_ne q C hD₀ (Finset.ne_of_mem_erase hD))
  have hsub : ∑ D ∈ Finset.univ.erase D₀,
      ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) ≤
        ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun _ _ _ ↦ Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hreal hc
  linarith

/-- **Mass of a block without a majority piece.**  If no piece has more than half of the
block, `c |C|` is at most `c` times the off-block points plus the boundary of the pieces. -/
theorem mul_card_model_le_of_no_majority [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) {c : ℝ} (hc : 0 ≤ c)
    (hexp : HasTaggedExpansionAtScale (A.blockAct C) c 1)
    (hsmall : ∀ D, 2 * (E.bridge q C D).source.card ≤ Fintype.card (E.model C)) :
    c * (Fintype.card (E.model C) : ℝ) ≤ c * ((E.offBlocks q C).card : ℝ) +
      ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) := by
  have hcard := E.card_model_le_sum_bridgeSource_add_offBlocks q C
  have hreal : (Fintype.card (E.model C) : ℝ) ≤
      ∑ D, ((E.bridge q C D).source.card : ℝ) + ((E.offBlocks q C).card : ℝ) := by
    exact_mod_cast hcard
  have hexpand := A.mul_sum_card_bridgeSource_le q C Finset.univ hexp fun D _ ↦ hsmall D
  have hmul := mul_le_mul_of_nonneg_left hreal hc
  linarith

end BlockAction

end BlockPatching
end GroupApproximation
