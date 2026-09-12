import GroupApproximation.KunThom.CentralizerBisectionRepresentationMassSum
import GroupApproximation.KunThom.CentralizerToBisectionDefect

/-!
# Totals of the piece charges

Forward half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4).  The mass bound of
`CentralizerBisectionRepresentationMassSum` is stated through the piece charges and
local obstructions of `q` and `q⁻¹`.  This file bounds their totals by the three
quantities that the approximation controls: the uncovered mass, the commutation
failures of `q` with the labels, and the compatibility failures of the block actions.

* `BlockAction.commutationMass A q` and `BlockAction.compatMass A`: the commutation
  failures of `q` and the compatibility failures, summed over the labels and blocks.
* `commutationMass_inv`: `q⁻¹` has the commutation failures of `q`.
* `sum_obstructionMass_le`: the local obstructions total at most
  `commutationMass q + 2 compatMass`.
* `sum_pieceCharge_le`: the piece charges total at most
  `c · #uncovered + 2 commutationMass q + 5 compatMass`.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

namespace BlockAction

variable {E : BlockEmbedding Y I} {L : Type*}

/-- The commutation failures of `q` with the labels, summed over the labels. -/
noncomputable def commutationMass [Fintype L] (A : BlockAction E L) (q : Equiv.Perm Y) : ℝ :=
  ∑ s : L, ((A.commutationFailure q s).card : ℝ)

/-- The compatibility failures of all blocks, summed over the labels. -/
noncomputable def compatMass [Fintype I] [Fintype L] (A : BlockAction E L) : ℝ :=
  ∑ s : L, ∑ C, ((A.compatFailure C s).card : ℝ)

/-- The inverse permutation has the commutation failures of the permutation. -/
theorem commutationMass_inv [Fintype L] (A : BlockAction E L) (q : Equiv.Perm Y) :
    A.commutationMass q⁻¹ = A.commutationMass q := by
  unfold commutationMass
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  unfold commutationFailure
  exact_mod_cast card_hammingDisagreement_inv_commutator q (A.act s)

/-- **Total local obstructions.** -/
theorem sum_obstructionMass_le [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) :
    ∑ C, A.obstructionMass q C ≤ A.commutationMass q + 2 * A.compatMass := by
  have h := A.sum_card_localObstruction_le q
  have hsplit : ∑ s : L, ((A.commutationFailure q s).card +
      2 * ∑ C, (A.compatFailure C s).card) =
      ∑ s : L, (A.commutationFailure q s).card +
        2 * ∑ s : L, ∑ C, (A.compatFailure C s).card := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hnat : ∑ C, ∑ s : L, (A.localObstruction q C s).card ≤
      ∑ s : L, (A.commutationFailure q s).card +
        2 * ∑ s : L, ∑ C, (A.compatFailure C s).card := by
    omega
  unfold obstructionMass commutationMass compatMass
  exact_mod_cast hnat

/-- **Total piece charge.** -/
theorem sum_pieceCharge_le [Fintype I] [Fintype L] (A : BlockAction E L) (q : Equiv.Perm Y)
    {c : ℝ} (hc : 0 ≤ c) :
    ∑ C, A.pieceCharge q c C ≤
      c * (E.uncovered.card : ℝ) + 2 * A.commutationMass q + 5 * A.compatMass := by
  classical
  have h₁ := E.sum_card_offBlocks_le q
  have h₂ : ∑ C, ∑ D, (taggedBoundary (A.blockAct C) (E.bridge q C D).source).card ≤
      ∑ C, ∑ s : L, (2 * (A.localObstruction q C s).card +
        (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ A.enteringFailure s).card) :=
    Finset.sum_le_sum fun C _ ↦ A.sum_card_taggedBoundary_bridgeSource_le q C
  have h₃ := A.sum_card_localObstruction_le q
  have h₄ : ∑ C, ∑ s : L, (Finset.univ.filter fun x : E.model C ↦
      q (E.embed C x) ∈ A.enteringFailure s).card ≤
      ∑ s : L, ∑ D, (A.compatFailure D s).card := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun s _ ↦ A.sum_card_filter_enteringFailure_le q s
  have h₅ : ∑ C, ∑ s : L, (2 * (A.localObstruction q C s).card +
      (Finset.univ.filter fun x : E.model C ↦ q (E.embed C x) ∈ A.enteringFailure s).card) =
      2 * ∑ C, ∑ s : L, (A.localObstruction q C s).card +
        ∑ C, ∑ s : L, (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ A.enteringFailure s).card := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h₆ : ∑ s : L, ((A.commutationFailure q s).card +
      2 * ∑ C, (A.compatFailure C s).card) =
      ∑ s : L, (A.commutationFailure q s).card +
        2 * ∑ s : L, ∑ C, (A.compatFailure C s).card := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hnat : ∑ C, ∑ D, (taggedBoundary (A.blockAct C) (E.bridge q C D).source).card ≤
      2 * ∑ s : L, (A.commutationFailure q s).card +
        5 * ∑ s : L, ∑ C, (A.compatFailure C s).card := by
    omega
  have hoff : ∑ C, ((E.offBlocks q C).card : ℝ) ≤ (E.uncovered.card : ℝ) := by
    exact_mod_cast h₁
  have hbd : ∑ C, ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) ≤
      2 * ∑ s : L, ((A.commutationFailure q s).card : ℝ) +
        5 * ∑ s : L, ∑ C, ((A.compatFailure C s).card : ℝ) := by
    exact_mod_cast hnat
  have hsplit : ∑ C, A.pieceCharge q c C = c * ∑ C, ((E.offBlocks q C).card : ℝ) +
      ∑ C, ∑ D, ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) := by
    unfold pieceCharge
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hmul := mul_le_mul_of_nonneg_left hoff hc
  unfold commutationMass compatMass
  rw [hsplit]
  linarith

end BlockAction

end BlockPatching
end GroupApproximation
