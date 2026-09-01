import GroupApproximation.GGT.DGOProposition414GapLocalLabel

/-!
# Connector letters in balanced-split auxiliary cycles

The mandatory connector targets use the reversed end connector on the left
and the start connector on the right.  This file identifies their literal
letters in the four-path auxiliary word and proves that they carry the exact
broken-source label chosen by the child dictionary.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Every labeled letter of a left connector remains a labeled letter after
the connector is reversed and placed at the start of an auxiliary cycle. -/
theorem isCompOf_auxiliaryCycle_leftConnector
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (hlabel : ∀ x ∈ left, x.IsCompOf lam) (r : ℕ)
    (hr : r < left.length)
    (hrCycle : r < (auxiliaryCycleWord left arc right chord).length) :
    ((auxiliaryCycleWord left arc right chord)[r]'hrCycle).IsCompOf lam := by
  have hrRev : r < (revWord left).length := by
    rw [OsinComponents.length_revWord]
    exact hr
  have ht : left.length - 1 - r < left.length := by omega
  have hrev : ((revWord left)[r]'hrRev).IsCompOf lam :=
    (isCompOf_getElem_revWord' left lam hrRev ht rfl).2
      (hlabel _ (List.getElem_mem ht))
  unfold auxiliaryCycleWord
  rw [List.getElem_append_left (by simp [OsinComponents.length_revWord]; omega),
    List.getElem_append_left (by simp [OsinComponents.length_revWord]; omega),
    List.getElem_append_left hrRev]
  exact hrev

/-- Every labeled letter of a right connector is the correspondingly shifted
labeled letter of the auxiliary cycle. -/
theorem isCompOf_auxiliaryCycle_rightConnector
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (hlabel : ∀ x ∈ right, x.IsCompOf lam) (r : ℕ)
    (hr : r < right.length)
    (hrCycle : left.length + arc.length + r <
      (auxiliaryCycleWord left arc right chord).length) :
    ((auxiliaryCycleWord left arc right chord)[left.length + arc.length + r]'hrCycle).IsCompOf lam := by
  have hrevLength : (revWord left).length = left.length :=
    OsinComponents.length_revWord left
  unfold auxiliaryCycleWord
  rw [List.getElem_append_left (by simp [OsinComponents.length_revWord]; omega),
    List.getElem_append_right (by simp [OsinComponents.length_revWord])]
  simpa [hrevLength] using hlabel (right[r]'hr) (List.getElem_mem hr)

namespace BalancedSplitData

/-- A first-half child's left connector is a literal component letter with
the exact label of its preceding broken source. -/
theorem firstGap_leftConnector_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hprev : HalfGap.previousEntry B.brokenAssignment.index.first j = some e)
    (r : ℕ) (hr : r < (B.firstGapLeft j).length)
    (hrCycle : r < (auxiliaryCycleWord (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))).length) :
    ((auxiliaryCycleWord (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)))[r]'hrCycle).IsCompOf
          (B.firstGapLocalLabel j r) := by
  let s := HalfEntry.entrySource B.brokenAssignment.index.first e
  have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
  rw [B.firstGapLocalLabel_leftConnector j e hprev r hr]
  exact isCompOf_auxiliaryCycle_leftConnector (P.label s)
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) (by
        intro x hx
        simp only [firstGapLeft] at hx
        rw [hprev] at hx
        exact (B.firstBrokenConnectors s hs).end_label x hx) r hr hrCycle

/-- A wrapped-half child's left connector is a literal component letter with
the exact label of its preceding broken source. -/
theorem secondGap_leftConnector_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hprev : HalfGap.previousEntry B.brokenAssignment.index.second j = some e)
    (r : ℕ) (hr : r < (B.secondGapLeft j).length)
    (hrCycle : r < (auxiliaryCycleWord (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))).length) :
    ((auxiliaryCycleWord (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)))[r]'hrCycle).IsCompOf
          (B.secondGapLocalLabel j r) := by
  let s := HalfEntry.entrySource B.brokenAssignment.index.second e
  have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
  rw [B.secondGapLocalLabel_leftConnector j e hprev r hr]
  exact isCompOf_auxiliaryCycle_leftConnector (P.label s)
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) (by
        intro x hx
        simp only [secondGapLeft] at hx
        rw [hprev] at hx
        exact (B.secondBrokenConnectors s hs).end_label x hx) r hr hrCycle

/-- A first-half child's right connector is a literal component letter with
the exact label of its following broken source. -/
theorem firstGap_rightConnector_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hnext : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (r : ℕ) (hr : r < (B.firstGapRight j).length)
    (hrCycle : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length + r <
      (auxiliaryCycleWord (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j))).length) :
    ((auxiliaryCycleWord (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j))).get ⟨
        List.length (B.firstGapLeft j) +
        List.length (arcWord B.firstArc B.firstArcCut
          (B.firstGapStartSide j) (B.firstGapFinishSide j)) + r,
        hrCycle⟩).IsCompOf
      (B.firstGapLocalLabel j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + r)) := by
  let s := HalfEntry.entrySource B.brokenAssignment.index.first e
  have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
  rw [B.firstGapLocalLabel_rightConnector j e hnext r hr]
  exact isCompOf_auxiliaryCycle_rightConnector (P.label s)
    (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j)) (by
        intro x hx
        simp only [firstGapRight] at hx
        rw [hnext] at hx
        exact (B.firstBrokenConnectors s hs).start_label x hx) r hr hrCycle

/-- A wrapped-half child's right connector is a literal component letter with
the exact label of its following broken source. -/
theorem secondGap_rightConnector_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hnext : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (r : ℕ) (hr : r < (B.secondGapRight j).length)
    (hrCycle : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length + r <
      (auxiliaryCycleWord (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)) (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j))).length) :
    ((auxiliaryCycleWord (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j))).get ⟨
        List.length (B.secondGapLeft j) +
        List.length (arcWord B.secondArc B.secondArcCut
          (B.secondGapStartSide j) (B.secondGapFinishSide j)) + r,
        hrCycle⟩).IsCompOf
      (B.secondGapLocalLabel j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + r)) := by
  let s := HalfEntry.entrySource B.brokenAssignment.index.second e
  have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
  rw [B.secondGapLocalLabel_rightConnector j e hnext r hr]
  exact isCompOf_auxiliaryCycle_rightConnector (P.label s)
    (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j)) (by
        intro x hx
        simp only [secondGapRight] at hx
        rw [hnext] at hx
        exact (B.secondBrokenConnectors s hs).start_label x hx) r hr hrCycle

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
