import GroupApproximation.GGT.DGOProposition414GapArcComponents

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

/-- The inherited arc's literal letters retain their labels at the shifted
positions of the auxiliary word. -/
theorem isCompOf_auxiliaryCycle_arc_iff
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (r : ℕ) (hr : r < arc.length)
    (hrCycle : left.length + r <
      (auxiliaryCycleWord left arc right chord).length) :
    ((auxiliaryCycleWord left arc right chord)[left.length + r]'hrCycle).IsCompOf lam ↔
      (arc[r]'hr).IsCompOf lam := by
  unfold auxiliaryCycleWord
  rw [List.getElem_append_left (by simp [OsinComponents.length_revWord]; omega),
    List.getElem_append_left (by simp [OsinComponents.length_revWord]; omega),
    List.getElem_append_right (by simp [OsinComponents.length_revWord])]
  simp [OsinComponents.length_revWord]

/-- A nonempty connector of length at most one occupies the initial singleton
component once its only nonvacuous boundary letter is excluded. -/
theorem isComp_auxiliaryCycle_leftConnector_of_boundary
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (hzero : 0 < left.length)
    (hlabel : ∀ x ∈ left, x.IsCompOf lam)
    (hnext : ∀ hn : 1 < (auxiliaryCycleWord left arc right chord).length,
      ¬ ((auxiliaryCycleWord left arc right chord)[1]'hn).IsCompOf lam) :
    IsComp lam (auxiliaryCycleWord left arc right chord) 0 1 := by
  have hcycle : 0 < (auxiliaryCycleWord left arc right chord).length := by
    simp [auxiliaryCycleWord, OsinComponents.length_revWord]
    omega
  apply isComp_singleton_of_boundary lam
    (auxiliaryCycleWord left arc right chord) hcycle
  · exact isCompOf_auxiliaryCycle_leftConnector lam left arc right chord
      hlabel 0 hzero hcycle
  · intro q hq
    omega
  · exact hnext

/-- A nonempty connector of length at most one occupies its shifted singleton
component once the two neighboring letters are excluded. -/
theorem isComp_auxiliaryCycle_rightConnector_of_boundary
    (lam : Λ) (left arc right chord : List (RelLetter G Λ))
    (hzero : 0 < right.length)
    (hlabel : ∀ x ∈ right, x.IsCompOf lam)
    (hprev : ∀ q : ℕ, left.length + arc.length = q + 1 →
      ∀ hq : q < (auxiliaryCycleWord left arc right chord).length,
      ¬ ((auxiliaryCycleWord left arc right chord)[q]'hq).IsCompOf lam)
    (hnext : ∀ hn : left.length + arc.length + 1 <
        (auxiliaryCycleWord left arc right chord).length,
      ¬ ((auxiliaryCycleWord left arc right chord).get
        ⟨left.length + arc.length + 1, hn⟩).IsCompOf lam) :
    IsComp lam (auxiliaryCycleWord left arc right chord)
      (left.length + arc.length) (left.length + arc.length + 1) := by
  have hp : left.length + arc.length <
      (auxiliaryCycleWord left arc right chord).length := by
    simp [auxiliaryCycleWord, OsinComponents.length_revWord]
    omega
  apply isComp_singleton_of_boundary lam
    (auxiliaryCycleWord left arc right chord) hp
  · exact isCompOf_auxiliaryCycle_rightConnector lam left arc right chord
      hlabel 0 hzero hp
  · exact hprev
  · exact hnext

namespace BalancedSplitData

/-- If a first-half gap has a nonempty inherited arc, its last literal letter
cannot have the label of the broken source immediately following the gap. -/
theorem firstGap_arcLast_not_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hnext : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (harc : 0 < (arcWord B.firstArc B.firstArcCut
      (B.firstGapStartSide j) (B.firstGapFinishSide j)).length) :
    ¬ ((arcWord B.firstArc B.firstArcCut
      (B.firstGapStartSide j) (B.firstGapFinishSide j)).get ⟨
        (arcWord B.firstArc B.firstArcCut
          (B.firstGapStartSide j) (B.firstGapFinishSide j)).length - 1,
        by omega⟩).IsCompOf
        (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
  let s := HalfEntry.entrySource B.brokenAssignment.index.first e
  have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
  change s ∈ brokenSet B.componentPlacement.firstTarget
    B.componentPlacement.firstSurvives at hs
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hfinish : B.firstGapFinishSide j = B.firstTargetSide s := by
    simp only [firstGapFinishSide]
    rw [hnext]
  have hfinishLe := B.firstGapFinishSide_le j
  have hcutEnd := B.firstArc_isCutPath.cut.le_length hfinishLe
  have harcLen : (arcWord B.firstArc B.firstArcCut
      (B.firstGapStartSide j) (B.firstGapFinishSide j)).length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) :=
    length_arcWord B.firstArc B.firstArcCut hcutEnd
  have htargetCut := (B.firstArcCut_target hsTarget).1
  have hfinishCut : B.firstArcCut (B.firstGapFinishSide j) =
      B.firstTargetPos s := by rw [hfinish, htargetCut]
  have hstartCut : B.firstArcCut (B.firstGapStartSide j) <
      B.firstTargetPos s := by
    rw [← hfinishCut]
    omega
  intro hletter
  let childArc := arcWord B.firstArc B.firstArcCut
    (B.firstGapStartSide j) (B.firstGapFinishSide j)
  have hchildLen : childArc.length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) := by
    simpa only [childArc] using harcLen
  have hi : childArc.length - 1 <
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) := by rw [hchildLen]; omega
  have hidxLen : childArc.length - 1 < childArc.length := by
    have hchildPos : 0 < childArc.length := by
      simpa only [childArc] using harc
    omega
  have hletter' : (childArc[childArc.length - 1]'hidxLen).IsCompOf
        (P.label s) := by
    simpa only [childArc, s, List.get_eq_getElem] using hletter
  dsimp [childArc] at hi hletter'
  rw [getElem_arcWord B.firstArc B.firstArcCut hcutEnd hi] at hletter'
  have hindex : B.firstArcCut (B.firstGapStartSide j) +
      ((arcWord B.firstArc B.firstArcCut
        (B.firstGapStartSide j) (B.firstGapFinishSide j)).length - 1) =
      B.firstTargetPos s - 1 := by omega
  have htargetLen : B.firstTargetPos s - 1 < B.firstArc.length := by
    have htargetLt := B.firstTargetPos_lt hsTarget
    omega
  have hget : B.firstArc[B.firstArcCut (B.firstGapStartSide j) +
      ((arcWord B.firstArc B.firstArcCut
        (B.firstGapStartSide j) (B.firstGapFinishSide j)).length - 1)] =
      B.firstArc[B.firstTargetPos s - 1] := getElem_congr_idx hindex
  have hletterTarget : (B.firstArc[B.firstTargetPos s - 1]'htargetLen).IsCompOf
      (P.label s) := by
    rw [← hget]
    exact hletter'
  exact (B.firstArc_targetComponent hsTarget).2.2.2.1
    (B.firstTargetPos s - 1) (by omega) htargetLen hletterTarget

/-- Wrapped-half counterpart of `firstGap_arcLast_not_isCompOf`. -/
theorem secondGap_arcLast_not_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hnext : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (harc : 0 < (arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j)).length) :
    ¬ ((arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j)).get ⟨
        (arcWord B.secondArc B.secondArcCut
          (B.secondGapStartSide j) (B.secondGapFinishSide j)).length - 1,
        by omega⟩).IsCompOf
        (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
  let s := HalfEntry.entrySource B.brokenAssignment.index.second e
  have hs := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
  change s ∈ brokenSet B.componentPlacement.secondTarget
    B.componentPlacement.secondSurvives at hs
  have hsTarget := (mem_brokenSet_iff.mp hs).1
  have hfinish : B.secondGapFinishSide j = B.secondTargetSide s := by
    simp only [secondGapFinishSide]
    rw [hnext]
  have hfinishLe := B.secondGapFinishSide_le j
  have hcutEnd := B.secondArc_isCutPath.cut.le_length hfinishLe
  have harcLen : (arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j)).length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) :=
    length_arcWord B.secondArc B.secondArcCut hcutEnd
  have htargetCut := (B.secondArcCut_target hsTarget).1
  have hfinishCut : B.secondArcCut (B.secondGapFinishSide j) =
      B.secondTargetPos s := by rw [hfinish, htargetCut]
  have hstartCut : B.secondArcCut (B.secondGapStartSide j) <
      B.secondTargetPos s := by
    rw [← hfinishCut]
    omega
  intro hletter
  let childArc := arcWord B.secondArc B.secondArcCut
    (B.secondGapStartSide j) (B.secondGapFinishSide j)
  have hchildLen : childArc.length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) := by
    simpa only [childArc] using harcLen
  have hi : childArc.length - 1 <
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) := by rw [hchildLen]; omega
  have hidxLen : childArc.length - 1 < childArc.length := by
    have hchildPos : 0 < childArc.length := by
      simpa only [childArc] using harc
    omega
  have hletter' : (childArc[childArc.length - 1]'hidxLen).IsCompOf
        (P.label s) := by
    simpa only [childArc, s, List.get_eq_getElem] using hletter
  dsimp [childArc] at hi hletter'
  rw [getElem_arcWord B.secondArc B.secondArcCut hcutEnd hi] at hletter'
  have hindex : B.secondArcCut (B.secondGapStartSide j) +
      ((arcWord B.secondArc B.secondArcCut
        (B.secondGapStartSide j) (B.secondGapFinishSide j)).length - 1) =
      B.secondTargetPos s - 1 := by omega
  have htargetLen : B.secondTargetPos s - 1 < B.secondArc.length := by
    have htargetLt := B.secondTargetPos_lt hsTarget
    omega
  have hget : B.secondArc[B.secondArcCut (B.secondGapStartSide j) +
      ((arcWord B.secondArc B.secondArcCut
        (B.secondGapStartSide j) (B.secondGapFinishSide j)).length - 1)] =
      B.secondArc[B.secondTargetPos s - 1] := getElem_congr_idx hindex
  have hletterTarget : (B.secondArc[B.secondTargetPos s - 1]'htargetLen).IsCompOf
      (P.label s) := by
    rw [← hget]
    exact hletter'
  exact (B.secondArc_targetComponent hsTarget).2.2.2.1
    (B.secondTargetPos s - 1) (by omega) htargetLen hletterTarget

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
        by_cases hf : B.firstGapRunsForward j
        · simp only [firstGapLeft] at hx
          rw [hprev] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.firstBrokenConnectors s hs).end_label x
            (by simpa only [s] using hx)
        · simp only [firstGapLeft] at hx
          rw [hprev] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.firstBrokenConnectors s hs).endThroughPartner_label x
            (by simpa only [s] using hx)) r hr hrCycle

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
        by_cases hf : B.secondGapRunsForward j
        · simp only [secondGapLeft] at hx
          rw [hprev] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.secondBrokenConnectors s hs).endThroughPartner_label x
            (by simpa only [s] using hx)
        · simp only [secondGapLeft] at hx
          rw [hprev] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.secondBrokenConnectors s hs).end_label x
            (by simpa only [s] using hx)) r hr hrCycle

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
        by_cases hf : B.firstGapRunsForward j
        · simp only [firstGapRight] at hx
          rw [hnext] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.firstBrokenConnectors s hs).start_label x
            (by simpa only [s] using hx)
        · simp only [firstGapRight] at hx
          rw [hnext] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.firstBrokenConnectors s hs).startThroughPartner_label x
            (by simpa only [s] using hx)) r hr hrCycle

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
        by_cases hf : B.secondGapRunsForward j
        · simp only [secondGapRight] at hx
          rw [hnext] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.secondBrokenConnectors s hs).startThroughPartner_label x
            (by simpa only [s] using hx)
        · simp only [secondGapRight] at hx
          rw [hnext] at hx
          simp only [hf, ↓reduceIte] at hx
          exact (B.secondBrokenConnectors s hs).start_label x
            (by simpa only [s] using hx)) r hr hrCycle

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
