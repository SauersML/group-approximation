import GroupApproximation.GGT.DGOProposition414GapPartition

/-!
# Balanced-half arc partitions

This file specializes the ordered gap partition to the broken distinguished
components in each balanced half of Dahmani--Guirardel--Osin Proposition 4.14.
It identifies the abstract gap endpoints with the canonical child endpoints
and proves the exact sum of all inherited child-arc side counts.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Broken first-half component sides in greedy source order. -/
noncomputable def firstBrokenSides
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : List ℕ :=
  List.ofFn fun e : Fin B.brokenAssignment.index.first.sources.length =>
    B.firstTargetSide
      (HalfEntry.entrySource B.brokenAssignment.index.first e)

/-- Broken wrapped-half component sides in greedy source order. -/
noncomputable def secondBrokenSides
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : List ℕ :=
  List.ofFn fun e : Fin B.brokenAssignment.index.second.sources.length =>
    B.secondTargetSide
      (HalfEntry.entrySource B.brokenAssignment.index.second e)

@[simp]
theorem firstBrokenSides_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstBrokenSides.length =
      (brokenSet B.componentPlacement.firstTarget
        B.componentPlacement.firstSurvives).card := by
  simp [firstBrokenSides,
    B.brokenAssignment.index.first.source_length]

@[simp]
theorem secondBrokenSides_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondBrokenSides.length =
      (brokenSet B.componentPlacement.secondTarget
        B.componentPlacement.secondSurvives).card := by
  simp [secondBrokenSides,
    B.brokenAssignment.index.second.source_length]

theorem firstBrokenSides_pairwise
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstBrokenSides.Pairwise (fun x y => x < y) := by
  classical
  rw [firstBrokenSides, List.pairwise_ofFn]
  intro e f hef
  let A := B.brokenAssignment.index.first
  let s := HalfEntry.entrySource A e
  let t := HalfEntry.entrySource A f
  have hs := HalfEntry.entrySource_mem A e
  have ht := HalfEntry.entrySource_mem A f
  have hle := List.pairwise_iff_getElem.mp A.source_order
    e.val f.val e.isLt f.isLt hef
  have hne := List.pairwise_iff_getElem.mp A.source_nodup
    e.val f.val e.isLt f.isLt hef
  have hpos : B.componentPlacement.firstPos s <
      B.componentPlacement.firstPos t := by
    rw [← HalfEntry.source_getElem_eq_pos_entrySource A e,
      ← HalfEntry.source_getElem_eq_pos_entrySource A f]
    exact lt_of_le_of_ne hle hne
  exact B.firstTargetSide_lt_of_pos_lt
    (mem_brokenSet_iff.mp hs).1 (mem_brokenSet_iff.mp ht).1 hpos

theorem secondBrokenSides_pairwise
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondBrokenSides.Pairwise (fun x y => x < y) := by
  classical
  rw [secondBrokenSides, List.pairwise_ofFn]
  intro e f hef
  let A := B.brokenAssignment.index.second
  let s := HalfEntry.entrySource A e
  let t := HalfEntry.entrySource A f
  have hs := HalfEntry.entrySource_mem A e
  have ht := HalfEntry.entrySource_mem A f
  have hle := List.pairwise_iff_getElem.mp A.source_order
    e.val f.val e.isLt f.isLt hef
  have hne := List.pairwise_iff_getElem.mp A.source_nodup
    e.val f.val e.isLt f.isLt hef
  have hpos : B.componentPlacement.secondPos s <
      B.componentPlacement.secondPos t := by
    rw [← HalfEntry.source_getElem_eq_pos_entrySource A e,
      ← HalfEntry.source_getElem_eq_pos_entrySource A f]
    exact lt_of_le_of_ne hle hne
  exact B.secondTargetSide_lt_of_pos_lt
    (mem_brokenSet_iff.mp hs).1 (mem_brokenSet_iff.mp ht).1 hpos

theorem firstBrokenSides_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    ∀ x ∈ B.firstBrokenSides, x < B.secondSide - B.firstSide + 1 := by
  rw [firstBrokenSides, List.forall_mem_ofFn_iff]
  intro e
  exact B.firstTargetSide_lt
    (mem_brokenSet_iff.mp
      (HalfEntry.entrySource_mem B.brokenAssignment.index.first e)).1

theorem secondBrokenSides_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    ∀ x ∈ B.secondBrokenSides,
      x < (n - B.secondSide) + B.firstSide + 1 := by
  rw [secondBrokenSides, List.forall_mem_ofFn_iff]
  intro e
  exact B.secondTargetSide_lt
    (mem_brokenSet_iff.mp
      (HalfEntry.entrySource_mem B.brokenAssignment.index.second e)).1

theorem firstGapStartSide_eq_orderedGapStart
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapStartSide j = orderedGapStart 0 B.firstBrokenSides j.val := by
  classical
  rcases j with ⟨j, hj⟩
  cases j with
  | zero => simp [firstGapStartSide, HalfGap.previousEntry, orderedGapStart]
  | succ j =>
      have hjlen : j < B.brokenAssignment.index.first.sources.length := by
        simp only [GreedyHalfFamilyIndex.pieceCount] at hj
        omega
      simp [firstGapStartSide, HalfGap.previousEntry, orderedGapStart,
        firstBrokenSides, hjlen]

theorem firstGapFinishSide_eq_orderedGapFinish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapFinishSide j = orderedGapFinish
      (B.secondSide - B.firstSide + 1) B.firstBrokenSides j.val := by
  classical
  rcases j with ⟨j, hj⟩
  by_cases h : j < B.brokenAssignment.index.first.sources.length
  · simp [firstGapFinishSide, HalfGap.nextEntry, orderedGapFinish,
      firstBrokenSides, h]
  · have hjlen : j = B.brokenAssignment.index.first.sources.length := by
      simp only [GreedyHalfFamilyIndex.pieceCount] at hj
      omega
    simp [firstGapFinishSide, HalfGap.nextEntry, orderedGapFinish,
      firstBrokenSides, hjlen]

theorem secondGapStartSide_eq_orderedGapStart
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapStartSide j = orderedGapStart 0 B.secondBrokenSides j.val := by
  classical
  rcases j with ⟨j, hj⟩
  cases j with
  | zero => simp [secondGapStartSide, HalfGap.previousEntry, orderedGapStart]
  | succ j =>
      have hjlen : j < B.brokenAssignment.index.second.sources.length := by
        simp only [GreedyHalfFamilyIndex.pieceCount] at hj
        omega
      simp [secondGapStartSide, HalfGap.previousEntry, orderedGapStart,
        secondBrokenSides, hjlen]

theorem secondGapFinishSide_eq_orderedGapFinish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapFinishSide j = orderedGapFinish
      ((n - B.secondSide) + B.firstSide + 1) B.secondBrokenSides j.val := by
  classical
  rcases j with ⟨j, hj⟩
  by_cases h : j < B.brokenAssignment.index.second.sources.length
  · simp [secondGapFinishSide, HalfGap.nextEntry, orderedGapFinish,
      secondBrokenSides, h]
  · have hjlen : j = B.brokenAssignment.index.second.sources.length := by
      simp only [GreedyHalfFamilyIndex.pieceCount] at hj
      omega
    simp [secondGapFinishSide, HalfGap.nextEntry, orderedGapFinish,
      secondBrokenSides, hjlen]

/-- First-half inherited child arcs omit exactly the broken first-half sides. -/
theorem sum_firstGap_arcSides_add_broken
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        (B.firstGapFinishSide j - B.firstGapStartSide j)) +
      (brokenSet B.componentPlacement.firstTarget
        B.componentPlacement.firstSurvives).card =
      B.secondSide - B.firstSide + 1 := by
  have hsum := sum_orderedGap_width_add_length 0
    (B.secondSide - B.firstSide + 1) B.firstBrokenSides
    (fun _ _ => Nat.zero_le _)
    B.firstBrokenSides_lt B.firstBrokenSides_pairwise
  calc
    (∑ j : Fin B.brokenAssignment.index.first.pieceCount,
        (B.firstGapFinishSide j - B.firstGapStartSide j)) +
        (brokenSet B.componentPlacement.firstTarget
          B.componentPlacement.firstSurvives).card =
      (∑ j : Fin (B.firstBrokenSides.length + 1),
        (orderedGapFinish (B.secondSide - B.firstSide + 1)
            B.firstBrokenSides j.val -
          orderedGapStart 0 B.firstBrokenSides j.val)) +
        B.firstBrokenSides.length := by
          apply congrArg₂ (· + ·)
          · let e : Fin B.brokenAssignment.index.first.pieceCount ≃
                Fin (B.firstBrokenSides.length + 1) :=
              finCongr (by simp [GreedyHalfFamilyIndex.pieceCount,
                firstBrokenSides])
            exact Fintype.sum_equiv e _ _ fun j => by
              rw [B.firstGapStartSide_eq_orderedGapStart,
                B.firstGapFinishSide_eq_orderedGapFinish]
              simp [e]
          · rw [B.firstBrokenSides_length]
    _ = B.secondSide - B.firstSide + 1 := by simpa using hsum

/-- Wrapped-half inherited child arcs omit exactly the broken wrapped sides. -/
theorem sum_secondGap_arcSides_add_broken
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    (∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        (B.secondGapFinishSide j - B.secondGapStartSide j)) +
      (brokenSet B.componentPlacement.secondTarget
        B.componentPlacement.secondSurvives).card =
      (n - B.secondSide) + B.firstSide + 1 := by
  have hsum := sum_orderedGap_width_add_length 0
    ((n - B.secondSide) + B.firstSide + 1) B.secondBrokenSides
    (fun _ _ => Nat.zero_le _)
    B.secondBrokenSides_lt B.secondBrokenSides_pairwise
  calc
    (∑ j : Fin B.brokenAssignment.index.second.pieceCount,
        (B.secondGapFinishSide j - B.secondGapStartSide j)) +
        (brokenSet B.componentPlacement.secondTarget
          B.componentPlacement.secondSurvives).card =
      (∑ j : Fin (B.secondBrokenSides.length + 1),
        (orderedGapFinish ((n - B.secondSide) + B.firstSide + 1)
            B.secondBrokenSides j.val -
          orderedGapStart 0 B.secondBrokenSides j.val)) +
        B.secondBrokenSides.length := by
          apply congrArg₂ (· + ·)
          · let e : Fin B.brokenAssignment.index.second.pieceCount ≃
                Fin (B.secondBrokenSides.length + 1) :=
              finCongr (by simp [GreedyHalfFamilyIndex.pieceCount,
                secondBrokenSides])
            exact Fintype.sum_equiv e _ _ fun j => by
              rw [B.secondGapStartSide_eq_orderedGapStart,
                B.secondGapFinishSide_eq_orderedGapFinish]
              simp [e]
          · rw [B.secondBrokenSides_length]
    _ = (n - B.secondSide) + B.firstSide + 1 := by simpa using hsum

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
