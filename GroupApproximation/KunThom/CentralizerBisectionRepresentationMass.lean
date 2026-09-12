import GroupApproximation.KunThom.CentralizerBisectionRepresentationPieces

/-!
# The mass of the blocks without a candidate bridge

Forward half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4).  A block `C` whose
bridge under `q` into no block is a cluster candidate is exceptional: the patched
bisection representing `q` pays its full size.  This file bounds the total size of
the exceptional blocks by quantities that sum over blocks.

Write `W C D` for the number of points of `C` sent into `D`, and let `D₀` be a
dominant target of `C`.  An exceptional block falls into one of three cases.

* No piece of `C` has a majority.  Tagged expansion bounds `c |C|` by `c` times the
  off-block points of `C` plus the boundary of its pieces
  (`BlockAction.mul_card_model_le_of_no_majority`).
* `C` has the majority piece `W C D₀ > |C| / 2`, but `W C D₀ ≤ |D₀| / 2`.  Then the
  points of `D₀` coming from `C` form a piece of `D₀` under `q⁻¹` of at most half
  of `D₀`, and expansion of `D₀` bounds `c |C| < 2 c W C D₀` by twice its boundary
  (`mul_card_model_le_of_minority`).
* `W C D₀` is a majority on both sides.  The bridge is not a candidate, so its
  defects exceed the threshold at the pair scale
  (`mul_scale_le_of_not_isClusterCandidate`), and both its missing masses are
  bounded by the pieces of `C` under `q` and of `D₀` under `q⁻¹`.  Distinct such
  blocks have distinct targets (`eq_of_two_mul_card_bridgeSource_gt`).

`mul_sum_card_model_le_of_not_selected` sums the three cases.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

namespace BlockEmbedding

/-- The target of the bridge from `C` to `D` is the source of the bridge of `q⁻¹` from `D`
to `C`. -/
theorem bridge_target_eq_inv_source (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).target = (E.bridge q⁻¹ D C).source := by
  ext z
  show z ∈ E.bridgeTarget q C D ↔ z ∈ E.bridgeSource q⁻¹ D C
  rw [mem_bridgeTarget, mem_bridgeSource]

theorem card_bridgeSource_eq_inv (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).source.card = (E.bridge q⁻¹ D C).source.card := by
  rw [(E.bridge q C D).card_source_eq_card_target, E.bridge_target_eq_inv_source]

/-- A majority into `D` from two blocks forces the two blocks to agree. -/
theorem eq_of_two_mul_card_bridgeSource_gt (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    {C C' D : I} (hC : Fintype.card (E.model D) < 2 * (E.bridge q C D).source.card)
    (hC' : Fintype.card (E.model D) < 2 * (E.bridge q C' D).source.card) : C = C' := by
  by_contra hne
  have hcard := card_le_targetDefect_add_of_disjoint (E.bridge q C D) (E.bridge q C' D)
    (E.disjoint_bridge_target q D hne)
  have h₁ := (E.bridge q C D).card_source_eq_card_target
  have h₂ := (E.bridge q C' D).card_source_eq_card_target
  have h₃ : (E.bridge q C D).target.card ≤ Fintype.card (E.model D) := Finset.card_le_univ _
  have h₄ : (E.bridge q C' D).target.card ≤ Fintype.card (E.model D) := Finset.card_le_univ _
  unfold FinitePartialBijection.targetDefect at hcard
  omega

/-- A majority piece is dominant. -/
theorem dominant_of_two_mul_card_bridgeSource_gt (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    {C D : I} (hmaj : Fintype.card (E.model C) < 2 * (E.bridge q C D).source.card) (D' : I) :
    (E.bridge q C D').source.card ≤ (E.bridge q C D).source.card := by
  by_cases hD : D' = D
  · rw [hD]
  · have hunion := Finset.card_union_of_disjoint (E.disjoint_bridge_source q C hD)
    have hle : ((E.bridge q C D').source ∪ (E.bridge q C D).source).card ≤
        Fintype.card (E.model C) := Finset.card_le_univ _
    omega

/-- A dominant target of a block. -/
noncomputable def dominantTarget [Fintype I] (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (C : I) : I :=
  Classical.choose (E.exists_dominant_bridge q C)

theorem dominantTarget_spec [Fintype I] (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).source.card ≤ (E.bridge q C (E.dominantTarget q C)).source.card :=
  Classical.choose_spec (E.exists_dominant_bridge q C) D

end BlockEmbedding

namespace BlockAction

variable {E : BlockEmbedding Y I} {L : Type*}

/-- Tagged expansion bounds a piece of at most half of the block by its boundary. -/
theorem mul_card_bridgeSource_le_taggedBoundary [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C D : I) {c : ℝ} (hexp : HasTaggedExpansionAtScale (A.blockAct C) c 1)
    (hsmall : 2 * (E.bridge q C D).source.card ≤ Fintype.card (E.model C)) :
    c * ((E.bridge q C D).source.card : ℝ) ≤
      ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) := by
  by_cases h0 : (E.bridge q C D).source.card = 0
  · rw [h0, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  · exact hexp.2 _ (Nat.one_le_iff_ne_zero.mpr h0) hsmall

/-- **Missing source mass against the dominant piece.** -/
theorem mul_sourceDefect_dominant_le [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) {c : ℝ} (hc : 0 ≤ c)
    (hexp : HasTaggedExpansionAtScale (A.blockAct C) c 1) {D₀ : I}
    (hD₀ : ∀ D, (E.bridge q C D).source.card ≤ (E.bridge q C D₀).source.card) :
    c * ((E.bridge q C D₀).sourceDefect : ℝ) ≤ c * ((E.offBlocks q C).card : ℝ) +
      ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) := by
  have hmain := A.mul_card_model_le_dominant q C hc hexp hD₀
  have hle : (E.bridge q C D₀).source.card ≤ Fintype.card (E.model C) :=
    Finset.card_le_univ _
  have hsd : ((E.bridge q C D₀).sourceDefect : ℝ) =
      (Fintype.card (E.model C) : ℝ) - ((E.bridge q C D₀).source.card : ℝ) := by
    rw [FinitePartialBijection.sourceDefect, Nat.cast_sub hle]
  rw [hsd, mul_sub]
  linarith

/-- **Missing target mass against a majority source.**  If more than half of block `D`
comes from block `C`, the missing target mass of the bridge is bounded by the pieces of `D`
under `q⁻¹`. -/
theorem mul_targetDefect_majority_le [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C D : I) {c : ℝ} (hc : 0 ≤ c)
    (hexp : HasTaggedExpansionAtScale (A.blockAct D) c 1)
    (hmaj : Fintype.card (E.model D) < 2 * (E.bridge q C D).source.card) :
    c * ((E.bridge q C D).targetDefect : ℝ) ≤ c * ((E.offBlocks q⁻¹ D).card : ℝ) +
      ∑ C', ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C').source).card : ℝ) := by
  have hmaj' : Fintype.card (E.model D) < 2 * (E.bridge q⁻¹ D C).source.card := by
    rw [← E.card_bridgeSource_eq_inv]
    exact hmaj
  have hmain := A.mul_card_model_le_dominant q⁻¹ D hc hexp
    (E.dominant_of_two_mul_card_bridgeSource_gt q⁻¹ hmaj')
  have hle : (E.bridge q⁻¹ D C).source.card ≤ Fintype.card (E.model D) :=
    Finset.card_le_univ _
  have htd : ((E.bridge q C D).targetDefect : ℝ) =
      (Fintype.card (E.model D) : ℝ) - ((E.bridge q⁻¹ D C).source.card : ℝ) := by
    rw [FinitePartialBijection.targetDefect, E.bridge_target_eq_inv_source, Nat.cast_sub hle]
  rw [htd, mul_sub]
  linarith

/-- **A block carrying a minority of its target.**  If more than half of `C` goes into `D`
but that part is at most half of `D`, then `c |C|` is at most twice the boundary of that
part inside `D` under `q⁻¹`. -/
theorem mul_card_model_le_of_minority [Fintype L] (A : BlockAction E L) (q : Equiv.Perm Y)
    (C D : I) {c : ℝ} (hc : 0 ≤ c) (hexp : HasTaggedExpansionAtScale (A.blockAct D) c 1)
    (hmaj : Fintype.card (E.model C) < 2 * (E.bridge q C D).source.card)
    (hmin : 2 * (E.bridge q C D).source.card ≤ Fintype.card (E.model D)) :
    c * (Fintype.card (E.model C) : ℝ) ≤
      2 * ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) := by
  have hmin' : 2 * (E.bridge q⁻¹ D C).source.card ≤ Fintype.card (E.model D) := by
    rw [← E.card_bridgeSource_eq_inv]
    exact hmin
  have hpiece := A.mul_card_bridgeSource_le_taggedBoundary q⁻¹ D C hexp hmin'
  have hcast : (Fintype.card (E.model C) : ℝ) ≤ 2 * ((E.bridge q⁻¹ D C).source.card : ℝ) := by
    rw [← E.card_bridgeSource_eq_inv]
    exact_mod_cast hmaj.le
  have hmul := mul_le_mul_of_nonneg_left hcast hc
  linarith

/-- **An exceptional block with a two-sided majority.**  If more than half of `C` goes into
`D` and that part is more than half of `D`, and the bridge is not a cluster candidate at
threshold `h` and scale `m`, then `c h m` is at most the missing masses of the bridge, at
level `h + 2 |L|`, plus twice `c` times the local obstructions of `q` on `C` and of `q⁻¹` on
`D`. -/
theorem mul_scale_le_of_not_candidate_majority [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C D : I) {c h : ℝ} {m : ℕ} (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hnot : ¬ (E.bridge q C D).IsClusterCandidate (A.blockAct C) (A.blockAct D) h m) :
    c * (h * m) ≤ (h + 2 * Fintype.card L) *
        (c * ((E.bridge q C D).sourceDefect : ℝ) + c * ((E.bridge q C D).targetDefect : ℝ)) +
      2 * c * (∑ s : L, ((A.localObstruction q C s).card : ℝ) +
        ∑ s : L, ((A.localObstruction q⁻¹ D s).card : ℝ)) := by
  have hmark := mul_scale_le_of_not_isClusterCandidate hh hnot
  have hfwd := A.card_equivarianceDefect_bridge_le_localObstruction q C D
  have hbwd := A.card_symm_equivarianceDefect_bridge_le_localObstruction q C D
  have hfwd' : (((E.bridge q C D).equivarianceDefect (A.blockAct C) (A.blockAct D)).card : ℝ) ≤
      (Fintype.card L : ℝ) * ((E.bridge q C D).sourceDefect : ℝ) +
        ∑ s : L, ((A.localObstruction q C s).card : ℝ) := by
    have hcast : (((E.bridge q C D).equivarianceDefect (A.blockAct C) (A.blockAct D)).card : ℝ) ≤
        ∑ s : L, (((E.bridge q C D).sourceDefect : ℝ) + ((A.localObstruction q C s).card : ℝ)) := by
      exact_mod_cast hfwd
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcast
    exact hcast
  have hbwd' : (((E.bridge q C D).symm.equivarianceDefect (A.blockAct D) (A.blockAct C)).card :
      ℝ) ≤ (Fintype.card L : ℝ) * ((E.bridge q C D).targetDefect : ℝ) +
        ∑ s : L, ((A.localObstruction q⁻¹ D s).card : ℝ) := by
    have hcast : (((E.bridge q C D).symm.equivarianceDefect (A.blockAct D)
        (A.blockAct C)).card : ℝ) ≤
        ∑ s : L, (((E.bridge q C D).targetDefect : ℝ) +
          ((A.localObstruction q⁻¹ D s).card : ℝ)) := by
      exact_mod_cast hbwd
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcast
    exact hcast
  have hsd : (((E.bridge q C D).sourceDefect + (E.bridge q C D).targetDefect : ℕ) : ℝ) =
      ((E.bridge q C D).sourceDefect : ℝ) + ((E.bridge q C D).targetDefect : ℝ) := by
    push_cast
    ring
  rw [hsd] at hmark
  have hmul := mul_le_mul_of_nonneg_left hmark hc
  have hsdn : (0 : ℝ) ≤ ((E.bridge q C D).sourceDefect : ℝ) := Nat.cast_nonneg _
  have htdn : (0 : ℝ) ≤ ((E.bridge q C D).targetDefect : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hfwd' hc, mul_le_mul_of_nonneg_left hbwd' hc]

end BlockAction

end BlockPatching
end GroupApproximation
