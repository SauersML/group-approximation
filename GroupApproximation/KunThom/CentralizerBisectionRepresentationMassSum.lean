import GroupApproximation.KunThom.CentralizerBisectionRepresentationMass

/-!
# The total mass of the exceptional blocks

Forward half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4).  This file sums the three
cases of `CentralizerBisectionRepresentationMass` over a set `U` of blocks whose bridges
under `q` are not cluster candidates.

* `BlockAction.pieceCharge A q c C`: `c` times the off-block points of `C` plus the
  boundary of the pieces of `C` under `q`.
* `BlockAction.obstructionMass A q C`: the local obstructions of `q` on `C`, summed over
  the labels.
* `mul_card_model_le_of_not_majority_pair` and `mul_card_model_le_of_majority_pair`: the
  per-block inequalities.
* `mul_sum_card_model_le_of_not_selected`: if two-sided majorities bound the block sizes
  by `K` times the pair scale, then `c h Σ_{C ∈ U} |C|` is at most
  `(h + K (h + 2 |L|))` times the charges of `q`, plus `(2 h + K (h + 2 |L|))` times the
  charges of `q⁻¹`, plus `2 K c` times the obstructions of `q` and of `q⁻¹`.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

/-- Sums of a nonnegative function along a map injective on a set are at most the total
sum. -/
theorem sum_comp_le_sum_of_injOn [Fintype I] (f : I → ℝ) (hf : ∀ D, 0 ≤ f D) (g : I → I)
    (S : Finset I) (hg : Set.InjOn g S) : ∑ C ∈ S, f (g C) ≤ ∑ D, f D := by
  classical
  rw [← Finset.sum_image hg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun D _ _ ↦ hf D

namespace BlockEmbedding

/-- More than half of block `C` goes into its dominant target, and that part is more than
half of the target. -/
abbrev IsMajorityPair [Fintype I] (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C : I) :
    Prop :=
  Fintype.card (E.model C) < 2 * (E.bridge q C (E.dominantTarget q C)).source.card ∧
    Fintype.card (E.model (E.dominantTarget q C)) <
      2 * (E.bridge q C (E.dominantTarget q C)).source.card

end BlockEmbedding

namespace BlockAction

variable {E : BlockEmbedding Y I} {L : Type*}

/-- The charge of the pieces of block `C` under `q`. -/
noncomputable def pieceCharge [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (c : ℝ) (C : I) : ℝ :=
  c * ((E.offBlocks q C).card : ℝ) +
    ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ)

/-- The local obstructions of `q` on block `C`, summed over the labels. -/
noncomputable def obstructionMass [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) : ℝ :=
  ∑ s : L, ((A.localObstruction q C s).card : ℝ)

theorem pieceCharge_nonneg [Fintype I] [Fintype L] (A : BlockAction E L) (q : Equiv.Perm Y)
    {c : ℝ} (hc : 0 ≤ c) (C : I) : 0 ≤ A.pieceCharge q c C :=
  add_nonneg (mul_nonneg hc (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)

theorem obstructionMass_nonneg [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) (C : I) : 0 ≤ A.obstructionMass q C :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- **An exceptional block without a two-sided majority.** -/
theorem mul_card_model_le_of_not_majority_pair [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hexp : ∀ C, HasTaggedExpansionAtScale (A.blockAct C) c 1) (C : I)
    (hpair : ¬ E.IsMajorityPair q C) :
    c * h * (Fintype.card (E.model C) : ℝ) ≤ h * A.pieceCharge q c C +
      2 * h * ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) := by
  unfold pieceCharge
  have hdom := E.dominantTarget_spec q C
  have hrow : (0 : ℝ) ≤ c * ((E.offBlocks q C).card : ℝ) +
      ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) :=
    add_nonneg (mul_nonneg hc (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  have hcol : (0 : ℝ) ≤
      ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) :=
    Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hsingle : ((taggedBoundary (A.blockAct (E.dominantTarget q C))
      (E.bridge q⁻¹ (E.dominantTarget q C) C).source).card : ℝ) ≤
      ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) :=
    Finset.single_le_sum (fun D _ ↦ Nat.cast_nonneg
      (taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card) (Finset.mem_univ _)
  have h2h : (0 : ℝ) ≤ 2 * h := by positivity
  have hrowh := mul_nonneg hh hrow
  have hcolh := mul_nonneg h2h hcol
  have hsingleh := mul_le_mul_of_nonneg_left hsingle h2h
  by_cases hmaj : Fintype.card (E.model C) <
      2 * (E.bridge q C (E.dominantTarget q C)).source.card
  · have hmin : 2 * (E.bridge q C (E.dominantTarget q C)).source.card ≤
        Fintype.card (E.model (E.dominantTarget q C)) := by
      by_contra hlt
      exact hpair ⟨hmaj, by omega⟩
    have hmain := A.mul_card_model_le_of_minority q C (E.dominantTarget q C) hc (hexp _)
      hmaj hmin
    have hmul := mul_le_mul_of_nonneg_left hmain hh
    linarith
  · have hsmall : ∀ D, 2 * (E.bridge q C D).source.card ≤ Fintype.card (E.model C) := by
      intro D
      have hD := hdom D
      omega
    have hmain := A.mul_card_model_le_of_no_majority q C hc (hexp C) hsmall
    have hmul := mul_le_mul_of_nonneg_left hmain hh
    linarith

/-- **An exceptional block with a two-sided majority.** -/
theorem mul_card_model_le_of_majority_pair [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) {c h K : ℝ} (m : I → I → ℕ) (hc : 0 ≤ c) (hh : 0 ≤ h) (hK0 : 0 ≤ K)
    (hexp : ∀ C, HasTaggedExpansionAtScale (A.blockAct C) c 1) (C : I)
    (hnot : ¬ (E.bridge q C (E.dominantTarget q C)).IsClusterCandidate (A.blockAct C)
      (A.blockAct (E.dominantTarget q C)) h (m C (E.dominantTarget q C)))
    (hcolmaj : Fintype.card (E.model (E.dominantTarget q C)) <
      2 * (E.bridge q C (E.dominantTarget q C)).source.card)
    (hscale : (Fintype.card (E.model C) : ℝ) ≤ K * m C (E.dominantTarget q C)) :
    c * h * (Fintype.card (E.model C) : ℝ) ≤
      K * ((h + 2 * Fintype.card L) *
        (A.pieceCharge q c C + A.pieceCharge q⁻¹ c (E.dominantTarget q C)) +
        2 * c * (A.obstructionMass q C + A.obstructionMass q⁻¹ (E.dominantTarget q C))) := by
  unfold pieceCharge obstructionMass
  have hdom := E.dominantTarget_spec q C
  have hmark := A.mul_scale_le_of_not_candidate_majority q C (E.dominantTarget q C) hc hh hnot
  have hsd := A.mul_sourceDefect_dominant_le q C hc (hexp C) hdom
  have htd := A.mul_targetDefect_majority_le q C (E.dominantTarget q C) hc (hexp _) hcolmaj
  have hch : 0 ≤ c * h := mul_nonneg hc hh
  have h₁ : c * h * (Fintype.card (E.model C) : ℝ) ≤
      c * h * (K * m C (E.dominantTarget q C)) :=
    mul_le_mul_of_nonneg_left hscale hch
  have h₂ := mul_le_mul_of_nonneg_left hmark hK0
  have hL : (0 : ℝ) ≤ h + 2 * Fintype.card L := by positivity
  have h₃ : (h + 2 * Fintype.card L) *
      (c * ((E.bridge q C (E.dominantTarget q C)).sourceDefect : ℝ) +
        c * ((E.bridge q C (E.dominantTarget q C)).targetDefect : ℝ)) ≤
      (h + 2 * Fintype.card L) *
        ((c * ((E.offBlocks q C).card : ℝ) +
          ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ)) +
        (c * ((E.offBlocks q⁻¹ (E.dominantTarget q C)).card : ℝ) +
          ∑ D, ((taggedBoundary (A.blockAct (E.dominantTarget q C))
            (E.bridge q⁻¹ (E.dominantTarget q C) D).source).card : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) hL
  have h₄ := mul_le_mul_of_nonneg_left h₃ hK0
  linarith

/-- **The total mass of the exceptional blocks.** -/
theorem mul_sum_card_model_le_of_not_selected [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) {c h K : ℝ} (m : I → I → ℕ) (hc : 0 ≤ c) (hh : 0 ≤ h) (hK0 : 0 ≤ K)
    (hexp : ∀ C, HasTaggedExpansionAtScale (A.blockAct C) c 1)
    (hK : ∀ C D, Fintype.card (E.model C) < 2 * (E.bridge q C D).source.card →
      Fintype.card (E.model D) < 2 * (E.bridge q C D).source.card →
        (Fintype.card (E.model C) : ℝ) ≤ K * m C D)
    (U : Finset I)
    (hU : ∀ C ∈ U, ∀ D, ¬ (E.bridge q C D).IsClusterCandidate (A.blockAct C) (A.blockAct D) h
      (m C D)) :
    c * h * ∑ C ∈ U, (Fintype.card (E.model C) : ℝ) ≤
      (h + K * (h + 2 * Fintype.card L)) * ∑ C, A.pieceCharge q c C +
        (2 * h + K * (h + 2 * Fintype.card L)) * ∑ D, A.pieceCharge q⁻¹ c D +
        2 * K * c * (∑ C, A.obstructionMass q C + ∑ D, A.obstructionMass q⁻¹ D) := by
  classical
  have hinj : Set.InjOn (E.dominantTarget q) (U.filter fun C ↦ E.IsMajorityPair q C :
      Finset I) := by
    intro C hC C' hC' heq
    have hPC := (Finset.mem_filter.mp (Finset.mem_coe.mp hC)).2
    have hPC' := (Finset.mem_filter.mp (Finset.mem_coe.mp hC')).2
    have h₂ : Fintype.card (E.model (E.dominantTarget q C)) <
        2 * (E.bridge q C' (E.dominantTarget q C)).source.card := by
      have h₃ := hPC'.2
      rw [← heq] at h₃
      exact h₃
    exact E.eq_of_two_mul_card_bridgeSource_gt q hPC.2 h₂
  have hA : ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
      c * h * (Fintype.card (E.model C) : ℝ) ≤
      K * (h + 2 * Fintype.card L) *
          ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C), A.pieceCharge q c C +
        K * (h + 2 * Fintype.card L) *
          ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
            A.pieceCharge q⁻¹ c (E.dominantTarget q C) +
        2 * K * c * ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C), A.obstructionMass q C +
        2 * K * c * ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
          A.obstructionMass q⁻¹ (E.dominantTarget q C) := by
    have hle : ∀ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
        c * h * (Fintype.card (E.model C) : ℝ) ≤
          K * (h + 2 * Fintype.card L) * A.pieceCharge q c C +
          K * (h + 2 * Fintype.card L) * A.pieceCharge q⁻¹ c (E.dominantTarget q C) +
          2 * K * c * A.obstructionMass q C +
          2 * K * c * A.obstructionMass q⁻¹ (E.dominantTarget q C) := by
      intro C hC
      have hCU := (Finset.mem_filter.mp hC).1
      have hPC := (Finset.mem_filter.mp hC).2
      have hbound := A.mul_card_model_le_of_majority_pair q m hc hh hK0 hexp C
        (hU C hCU (E.dominantTarget q C)) hPC.2 (hK C _ hPC.1 hPC.2)
      linarith
    calc ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
          c * h * (Fintype.card (E.model C) : ℝ)
        ≤ ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
            (K * (h + 2 * Fintype.card L) * A.pieceCharge q c C +
            K * (h + 2 * Fintype.card L) * A.pieceCharge q⁻¹ c (E.dominantTarget q C) +
            2 * K * c * A.obstructionMass q C +
            2 * K * c * A.obstructionMass q⁻¹ (E.dominantTarget q C)) :=
          Finset.sum_le_sum hle
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hB : ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C),
      c * h * (Fintype.card (E.model C) : ℝ) ≤
      h * ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C), A.pieceCharge q c C +
        2 * h * ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C),
          ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) := by
    calc ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C),
          c * h * (Fintype.card (E.model C) : ℝ)
        ≤ ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C), (h * A.pieceCharge q c C +
            2 * h * ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card :
              ℝ)) :=
          Finset.sum_le_sum fun C hC ↦
            A.mul_card_model_le_of_not_majority_pair q hc hh hexp C (Finset.mem_filter.mp hC).2
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hS₁ : ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C), A.pieceCharge q c C ≤
      ∑ C, A.pieceCharge q c C :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun C _ _ ↦ A.pieceCharge_nonneg q hc C
  have hS₂ : ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
      A.pieceCharge q⁻¹ c (E.dominantTarget q C) ≤ ∑ D, A.pieceCharge q⁻¹ c D :=
    sum_comp_le_sum_of_injOn (A.pieceCharge q⁻¹ c) (A.pieceCharge_nonneg q⁻¹ hc)
      (E.dominantTarget q) _ hinj
  have hS₃ : ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C), A.obstructionMass q C ≤
      ∑ C, A.obstructionMass q C :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun C _ _ ↦ A.obstructionMass_nonneg q C
  have hS₄ : ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
      A.obstructionMass q⁻¹ (E.dominantTarget q C) ≤ ∑ D, A.obstructionMass q⁻¹ D :=
    sum_comp_le_sum_of_injOn (A.obstructionMass q⁻¹) (A.obstructionMass_nonneg q⁻¹)
      (E.dominantTarget q) _ hinj
  have hS₅ : ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C), A.pieceCharge q c C ≤
      ∑ C, A.pieceCharge q c C :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun C _ _ ↦ A.pieceCharge_nonneg q hc C
  have hS₆ : ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C),
      ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) ≤
        ∑ D, A.pieceCharge q⁻¹ c D := by
    calc ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C),
          ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ)
        ≤ ∑ C, ∑ D, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun C _ _ ↦
            Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
      _ = ∑ D, ∑ C, ((taggedBoundary (A.blockAct D) (E.bridge q⁻¹ D C).source).card : ℝ) :=
          Finset.sum_comm
      _ ≤ ∑ D, A.pieceCharge q⁻¹ c D :=
          Finset.sum_le_sum fun D _ ↦
            le_add_of_nonneg_left (mul_nonneg hc (Nat.cast_nonneg _))
  have hsplit : ∑ C ∈ U.filter (fun C ↦ E.IsMajorityPair q C),
      c * h * (Fintype.card (E.model C) : ℝ) +
      ∑ C ∈ U.filter (fun C ↦ ¬ E.IsMajorityPair q C),
        c * h * (Fintype.card (E.model C) : ℝ) =
      ∑ C ∈ U, c * h * (Fintype.card (E.model C) : ℝ) :=
    Finset.sum_filter_add_sum_filter_not U (fun C ↦ E.IsMajorityPair q C) _
  have hmulsum : c * h * ∑ C ∈ U, (Fintype.card (E.model C) : ℝ) =
      ∑ C ∈ U, c * h * (Fintype.card (E.model C) : ℝ) :=
    Finset.mul_sum _ _ _
  have hLn : (0 : ℝ) ≤ h + 2 * Fintype.card L := by positivity
  have hKL : 0 ≤ K * (h + 2 * Fintype.card L) := mul_nonneg hK0 hLn
  have hKc : 0 ≤ 2 * K * c := by positivity
  have h2h : (0 : ℝ) ≤ 2 * h := by positivity
  have p₁ := mul_le_mul_of_nonneg_left hS₁ hKL
  have p₂ := mul_le_mul_of_nonneg_left hS₂ hKL
  have p₃ := mul_le_mul_of_nonneg_left hS₃ hKc
  have p₄ := mul_le_mul_of_nonneg_left hS₄ hKc
  have p₅ := mul_le_mul_of_nonneg_left hS₅ hh
  have p₆ := mul_le_mul_of_nonneg_left hS₆ h2h
  linarith

end BlockAction

end BlockPatching
end GroupApproximation
