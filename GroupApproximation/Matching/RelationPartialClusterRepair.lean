import GroupApproximation.Kazhdan.KazhdanImprovement
import GroupApproximation.Matching.PartialSwapEquivariance
import GroupApproximation.Matching.PartialClusterPresentation

/-!
# Partial-cluster repair from an arbitrary finite relation

This file is the finite combinatorial bridge from relation rounding to the
partial-cluster machinery.  The labels are arbitrary finite families of
permutations; in particular, no exact group action and no stability theorem is
assumed.  A relation close to the graph of a partial-bijection swap is repaired
by retaining its singleton row/column core and completing that core to a
permutation.  Explicit edit and diagonal-boundary budgets then make the
left-to-right crossing a cluster candidate close to the original arrow.
-/

namespace GroupApproximation
namespace RelationPartialClusterRepair

open AlmostAutomorphism
open FinitePartialBijection
open KazhdanImprovement

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {Y Z : FiniteModel}

/-- The number of permutation points which the singleton-core completion may
change, expressed only through the symmetric edit distance of the input
relation from the graph of the original swap. -/
def disagreementBudget (b : FinitePartialBijection Y Z)
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) : ℕ :=
  (permutationGraph (sumModel Y Z) b.swapPerm \ U).card +
    2 * ((permutationGraph (sumModel Y Z) b.swapPerm \ U).card +
      (U \ permutationGraph (sumModel Y Z) b.swapPerm).card)

/-- The bad-arc budget for the completed singleton core.  It combines the
diagonal boundary of the input relation with the edit cost of extracting and
completing its biunique core. -/
def badArcBudget (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) : ℕ :=
  (relationBoundary (sumModel Y Z)
      (Finset.univ.image (sumAction actY actZ)) U).card +
    7 * (Finset.univ.image (sumAction actY actZ)).card *
      ((permutationGraph (sumModel Y Z) b.swapPerm \ U).card +
        (U \ permutationGraph (sumModel Y Z) b.swapPerm).card)

/-- Repair a relation on the disjoint union and retain its left-to-right
crossing as a finite partial bijection. -/
noncomputable def repair
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) : FinitePartialBijection Y Z :=
  extractCrossing (repairRelation (sumModel Y Z) U)

/-- The completed singleton core differs from the original swap on at most
the explicit relation edit budget. -/
theorem card_hammingDisagreement_repair_le
    (b : FinitePartialBijection Y Z)
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) :
    (hammingDisagreement b.swapPerm
      (repairRelation (sumModel Y Z) U)).card ≤ disagreementBudget b U := by
  have h := card_repairRelation_disagreement_le
    (sumModel Y Z) U b.swapPerm
  have hcomm :
      hammingDisagreement b.swapPerm (repairRelation (sumModel Y Z) U) =
        hammingDisagreement (repairRelation (sumModel Y Z) U) b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  rw [hcomm]
  exact h

/-- The repaired permutation has no more bad arcs than the explicit boundary
and edit budget. -/
theorem card_badArcs_repair_le
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) :
    (badArcs (sumModel Y Z) (Finset.univ.image (sumAction actY actZ))
      (repairRelation (sumModel Y Z) U)).card ≤
        badArcBudget actY actZ b U := by
  exact card_badArcs_repairRelation_le (sumModel Y Z)
    (Finset.univ.image (sumAction actY actZ)) U b.swapPerm

/-- Complete finite interface from relation rounding to a cluster candidate.
The three hypotheses are pure numerical inequalities involving only the
original partial arrow, the edit distance of `U` from its swap graph, and the
diagonal boundary of `U`. -/
theorem repair_candidate_and_close_of_bounds
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z)))
    {h : ℝ} {m : ℕ}
    (hself : b.sourceDefect + b.targetDefect +
      2 * disagreementBudget b U < 2 * m)
    (hforward :
      ((2 * (Fintype.card L *
          (b.sourceDefect + disagreementBudget b U)) +
        Fintype.card L * badArcBudget actY actZ b U : ℕ) : ℝ) <
          h * m / 2)
    (hbackward :
      ((2 * (Fintype.card L *
          (b.targetDefect + disagreementBudget b U)) +
        Fintype.card L * badArcBudget actY actZ b U : ℕ) : ℝ) <
          h * m / 2) :
    (repair U).IsClusterCandidate actY actZ h m ∧
      (repair U).twoSidedDisagreement b < 2 * m := by
  let p := repairRelation (sumModel Y Z) U
  have hham : (hammingDisagreement b.swapPerm p).card ≤
      disagreementBudget b U := by
    simpa only [p] using card_hammingDisagreement_repair_le b U
  have hsource : (extractCrossing p).sourceDefect ≤
      b.sourceDefect + disagreementBudget b U := by
    exact (sourceDefect_extractCrossing_le b p).trans (Nat.add_le_add_left hham _)
  have htargetBase := targetDefect_extractCrossing_le b p
  rw [card_hammingDisagreement_inv] at htargetBase
  have htarget : (extractCrossing p).targetDefect ≤
      b.targetDefect + disagreementBudget b U := by
    exact htargetBase.trans (Nat.add_le_add_left hham _)
  have hcandSelf : (extractCrossing p).sourceDefect +
      (extractCrossing p).targetDefect < 2 * m := by
    omega
  have hbad :
      (badArcs (sumModel Y Z) (Finset.univ.image (sumAction actY actZ))
        p).card ≤ badArcBudget actY actZ b U := by
    simpa only [p] using card_badArcs_repair_le actY actZ b U
  have htagBase :=
    card_sumCommutationDefect_le_card_mul_badArcs p actY actZ
  have htag : (sumCommutationDefect p actY actZ).card ≤
      Fintype.card L * badArcBudget actY actZ b U :=
    htagBase.trans (Nat.mul_le_mul_left _ hbad)
  have htagInvBase :=
    card_sumCommutationDefect_le_card_mul_badArcs p⁻¹ actY actZ
  rw [card_badArcs_inv] at htagInvBase
  have htagInv : (sumCommutationDefect p⁻¹ actY actZ).card ≤
      Fintype.card L * badArcBudget actY actZ b U :=
    htagInvBase.trans (Nat.mul_le_mul_left _ hbad)
  have hforwardNat :
      2 * (Fintype.card L * (extractCrossing p).sourceDefect) +
          (sumCommutationDefect p actY actZ).card ≤
        2 * (Fintype.card L *
          (b.sourceDefect + disagreementBudget b U)) +
          Fintype.card L * badArcBudget actY actZ b U := by
    omega
  have hforwardReal :
      ((2 * (Fintype.card L * (extractCrossing p).sourceDefect) +
        (sumCommutationDefect p actY actZ).card : ℕ) : ℝ) < h * m / 2 := by
    exact (by exact_mod_cast hforwardNat).trans_lt hforward
  have hbackwardNat :
      2 * (Fintype.card L * (extractCrossing p).targetDefect) +
          (sumCommutationDefect p⁻¹ actY actZ).card ≤
        2 * (Fintype.card L *
          (b.targetDefect + disagreementBudget b U)) +
          Fintype.card L * badArcBudget actY actZ b U := by
    omega
  have hbackwardReal :
      ((2 * (Fintype.card L * (extractCrossing p).targetDefect) +
        (sumCommutationDefect p⁻¹ actY actZ).card : ℕ) : ℝ) < h * m / 2 := by
    exact (by exact_mod_cast hbackwardNat).trans_lt hbackward
  have hcand := isClusterCandidate_extractCrossing_of_bounds p actY actZ
    hcandSelf hforwardReal hbackwardReal
  have hcloseBase := twoSidedDisagreement_extractCrossing_le_self_add_two_mul b p
  have hclose : b.twoSidedDisagreement (extractCrossing p) < 2 * m := by
    omega
  refine ⟨?_, ?_⟩
  · simpa only [repair, p] using hcand
  · rw [twoSidedDisagreement_comm]
    simpa only [repair, p] using hclose

end RelationPartialClusterRepair

universe u

namespace PartialClusterSystem

open RelationPartialClusterRepair

variable {I : Type u} [Fintype I]
variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Build a partial cluster system from finite relation improvements.  This
constructor isolates the exact remaining obligation in the approximate-action
case: for each composite candidate, produce one relation satisfying the three
explicit numerical bounds.  The conversion of that relation into an improved
candidate is entirely internal. -/
noncomputable def ofRelationRepairs
    (model : I → FiniteModel)
    (act : ∀ X, L → Equiv.Perm (model X))
    (h : ℝ) (h_pos : 0 < h) (scale : ℕ) (scale_pos : 0 < scale)
    (expands : ∀ X,
      FinitePartialBijection.HasTaggedExpansionAtScale
        (act X) h scale)
    (size : ∀ X, 17 * scale ≤ Fintype.card (model X))
    (relationExists : ∀ {X Y Z}
      (f : FinitePartialBijection (model X) (model Y)),
      f.IsClusterCandidate (act X) (act Y) h scale →
      ∀ (g : FinitePartialBijection (model Y) (model Z)),
      g.IsClusterCandidate (act Y) (act Z) h scale →
        ∃ U : Finset (((model X) ⊕ (model Z)) ×
            ((model X) ⊕ (model Z))),
          let b := f.trans g
          b.sourceDefect + b.targetDefect +
              2 * disagreementBudget b U < 2 * scale ∧
            ((2 * (Fintype.card L *
                (b.sourceDefect + disagreementBudget b U)) +
              Fintype.card L * badArcBudget (act X) (act Z) b U : ℕ) : ℝ) <
                h * scale / 2 ∧
            ((2 * (Fintype.card L *
                (b.targetDefect + disagreementBudget b U)) +
              Fintype.card L * badArcBudget (act X) (act Z) b U : ℕ) : ℝ) <
                h * scale / 2) :
    PartialClusterSystem I L where
  model := model
  act := act
  h := h
  h_pos := h_pos
  scale := scale
  scale_pos := scale_pos
  expands := expands
  size := size
  improveExists := by
    intro X Y Z f hf g hg
    obtain ⟨U, hself, hforward, hbackward⟩ := relationExists f hf g hg
    exact ⟨RelationPartialClusterRepair.repair U,
      repair_candidate_and_close_of_bounds
        (act X) (act Z) (f.trans g) U hself hforward hbackward⟩

end PartialClusterSystem
end GroupApproximation
