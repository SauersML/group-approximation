import GroupApproximation.GGT.DGOProposition414GapLeftConnector

/-!
# The left connector of a wrapped Proposition 4.14 gap child

Wrapped counterpart of `DGOProposition414GapLeftConnector`.  The three cases
for the letter following the connector are the same: an inherited arc letter,
the right connector when the gap arc is empty, or the head of the child chord
when both are empty, the last being the residual
`SecondGapLeftConnectorChordSeam`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## The initial inherited arc letter -/

/-- The initial letter of a nonempty wrapped gap arc is the parent letter just
after the preceding broken source, so it does not carry that source's
label. -/
theorem secondGap_arcFirst_not_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (harc : 0 < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length) :
    ¬ ((arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j))[0]'harc).IsCompOf
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p)) := by
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second p
  have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
  have hcutEnd : B.secondArcCut (B.secondGapFinishSide j) ≤ B.secondArc.length :=
    B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j)
  have harcLen : (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length =
      B.secondArcCut (B.secondGapFinishSide j) -
        B.secondArcCut (B.secondGapStartSide j) :=
    length_arcWord B.secondArc B.secondArcCut hcutEnd
  have hstartSide : B.secondGapStartSide j =
      B.secondTargetSide (HalfEntry.entrySource
        B.brokenAssignment.index.second p) + 1 := by
    simp only [secondGapStartSide]
    rw [hp]
  have hcutStart : B.secondArcCut (B.secondGapStartSide j) =
      B.secondTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.second p) + 1 := by
    rw [hstartSide]
    exact (B.secondArcCut_target hpTarget).2
  have hi : 0 < B.secondArcCut (B.secondGapFinishSide j) -
      B.secondArcCut (B.secondGapStartSide j) := by omega
  have hlt : B.secondTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.second p) + 1 < B.secondArc.length := by omega
  intro hletter
  rw [getElem_arcWord B.secondArc B.secondArcCut hcutEnd hi] at hletter
  have hidx : B.secondArcCut (B.secondGapStartSide j) + 0 =
      B.secondTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.second p) + 1 := by omega
  have hparent : (B.secondArc[B.secondTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.second p) + 1]'hlt).IsCompOf
      (P.label (HalfEntry.entrySource
        B.brokenAssignment.index.second p)) := by
    rw [← getElem_congr_idx (c := B.secondArc) hidx]
    exact hletter
  exact (B.secondArc_targetComponent hpTarget).2.2.2.2 hlt hparent

/-! ## The residual chord seam at a left connector -/

/-- The chord-seam exclusion for a second-half left connector: when the gap arc
and the right connector are both empty, the head of the child chord does not
carry the preceding broken source's label. -/
def SecondGapLeftConnectorChordSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : Prop :=
  (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length = 0 →
    (B.secondGapRight j).length = 0 →
    ∀ hn : 1 < (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[1]'hn).IsCompOf (B.secondGapLocalLabel j 0)

/-- A nonempty gap arc makes the left-connector chord seam vacuous. -/
theorem secondGapLeftConnectorChordSeam_of_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (harc : 0 < (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)).length) :
    SecondGapLeftConnectorChordSeam B j := by
  intro hA0
  exact absurd hA0 (by omega)

/-- A nonempty right connector makes the left-connector chord seam vacuous. -/
theorem secondGapLeftConnectorChordSeam_of_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hright : 0 < (B.secondGapRight j).length) :
    SecondGapLeftConnectorChordSeam B j := by
  intro _ hR0
  exact absurd hR0 (by omega)

/-- The degenerate empty-cycle model satisfies the left-connector chord
seam. -/
theorem secondGapLeftConnectorChordSeam_of_emptyCycle
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (hcycle : B.secondGapCycle j = []) :
    SecondGapLeftConnectorChordSeam B j := by
  intro _ _ hn
  exact absurd hn (by rw [hcycle]; simp)

/-! ## The successor exclusion for a second-half left connector -/

/-- The letter after a second-half left connector does not carry that
connector's label. -/
theorem secondGap_leftConnector_next_exclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hzero : 0 < (B.secondGapLeft j).length)
    (hseam : SecondGapLeftConnectorChordSeam B j) :
    ∀ hn : 1 < (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[1]'hn).IsCompOf
        (B.secondGapLocalLabel j 0) := by
  classical
  intro hn hletter
  have hone : (B.secondGapLeft j).length = 1 := by
    have hle := B.secondGapLeft_length_le_one j
    omega
  have hlab : B.secondGapLocalLabel j 0 =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second p) :=
    B.secondGapLocalLabel_leftConnector j p hp 0 hzero
  rw [hlab] at hletter
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.second p
  have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
  by_cases harc : 0 < (arcWord B.secondArc B.secondArcCut
      (B.secondGapStartSide j) (B.secondGapFinishSide j)).length
  · have hcycleLt : (B.secondGapLeft j).length + 0 <
        (B.secondGapCycle j).length := by omega
    have hgetEq : (B.secondGapCycle j)[1]'hn =
        (B.secondGapCycle j)[(B.secondGapLeft j).length + 0]'hcycleLt :=
      getElem_congr_idx (by omega)
    rw [hgetEq] at hletter
    have hco := (isCompOf_auxiliaryCycle_arc_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.second p))
      (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j)
        (B.secondGapChordFinish j)) 0 harc hcycleLt).mp hletter
    exact B.secondGap_arcFirst_not_isCompOf j p hp harc hco
  · have hA0 : (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)).length = 0 := by omega
    by_cases hright : 0 < (B.secondGapRight j).length
    · have hnxt : HalfGap.nextEntry B.brokenAssignment.index.second j
          ≠ none := by
        intro hnone
        have h0 : (B.secondGapRight j).length = 0 := by
          simp only [secondGapRight]
          rw [hnone]
          simp
        omega
      obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
      have he : HalfGap.nextEntry B.brokenAssignment.index.second j =
          some e := by simpa using he'
      have hcycleLt : (B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length + 0 <
          (B.secondGapCycle j).length := by omega
      have hgetEq : (B.secondGapCycle j)[1]'hn =
          (B.secondGapCycle j)[(B.secondGapLeft j).length +
            (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)).length + 0]'hcycleLt :=
        getElem_congr_idx (by omega)
      rw [hgetEq] at hletter
      have hconn := B.secondGap_rightConnector_isCompOf j e he 0 hright hcycleLt
      have hrlab : B.secondGapLocalLabel j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + 0) =
          P.label (HalfEntry.entrySource
            B.brokenAssignment.index.second e) :=
        B.secondGapLocalLabel_rightConnector j e he 0 hright
      rw [hrlab] at hconn
      have hconn' : ((B.secondGapCycle j)[(B.secondGapLeft j).length +
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length + 0]'hcycleLt).IsCompOf
          (P.label (HalfEntry.entrySource
            B.brokenAssignment.index.second e)) := by
        simpa [List.get_eq_getElem] using hconn
      have hEqLabel : P.label (HalfEntry.entrySource
            B.brokenAssignment.index.second p) =
          P.label (HalfEntry.entrySource
            B.brokenAssignment.index.second e) :=
        eq_of_isCompOf_of_isCompOf hletter hconn'
      have heBroken := HalfEntry.entrySource_mem
        B.brokenAssignment.index.second e
      have heTarget := (mem_brokenSet_iff.mp heBroken).1
      have hstartSide : B.secondGapStartSide j =
          B.secondTargetSide (HalfEntry.entrySource
            B.brokenAssignment.index.second p) + 1 := by
        simp only [secondGapStartSide]
        rw [hp]
      have hfinishSide : B.secondGapFinishSide j =
          B.secondTargetSide (HalfEntry.entrySource
            B.brokenAssignment.index.second e) := by
        simp only [secondGapFinishSide]
        rw [he]
      have hcutEnd : B.secondArcCut (B.secondGapFinishSide j) ≤
          B.secondArc.length :=
        B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j)
      have harcLen : (arcWord B.secondArc B.secondArcCut
          (B.secondGapStartSide j) (B.secondGapFinishSide j)).length =
          B.secondArcCut (B.secondGapFinishSide j) -
            B.secondArcCut (B.secondGapStartSide j) :=
        length_arcWord B.secondArc B.secondArcCut hcutEnd
      have hcutStart : B.secondArcCut (B.secondGapStartSide j) =
          B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second p) + 1 := by
        rw [hstartSide]
        exact (B.secondArcCut_target hpTarget).2
      have hcutFinish : B.secondArcCut (B.secondGapFinishSide j) =
          B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second e) := by
        rw [hfinishSide]
        exact (B.secondArcCut_target heTarget).1
      have hposLt : B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second p) <
          B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second e) :=
        HalfGap.pos_entrySource_lt_of_adjacent
          B.brokenAssignment.index.second j hp he
      have hadj : B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second p) + 1 =
          B.secondTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.second e) := by omega
      exact B.secondTarget_label_ne_of_succ hpTarget heTarget hadj hEqLabel
    · rw [← hlab] at hletter
      exact hseam hA0 (by omega) hn hletter

/-! ## The left connector component -/

/-- A second-half left connector is a maximal one-letter component of its
auxiliary cycle, given the residual chord seam. -/
theorem secondGap_leftConnector_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (p : Fin B.brokenAssignment.index.second.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.second j = some p)
    (hzero : 0 < (B.secondGapLeft j).length)
    (hseam : SecondGapLeftConnectorChordSeam B j) :
    IsComp (B.secondGapLocalLabel j 0) (B.secondGapCycle j)
      (B.secondGapCut j 0) (B.secondGapCut j 1) :=
  B.secondGap_leftConnector_cycleComponent j p hp hzero
    (B.secondGap_leftConnector_next_exclusion j p hp hzero hseam)

/-- The `leftComponent` field of `SecondGapComponentFamily`, from the residual
chord seam alone. -/
theorem secondGap_leftComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (r : ℕ) (hr : r < (B.secondGapLeft j).length)
    (hseam : SecondGapLeftConnectorChordSeam B j) :
    IsComp (B.secondGapLocalLabel j r) (B.secondGapCycle j)
      (B.secondGapCut j r) (B.secondGapCut j (r + 1)) := by
  classical
  have hle := B.secondGapLeft_length_le_one j
  have hr0 : r = 0 := by omega
  subst hr0
  have hzero : 0 < (B.secondGapLeft j).length := by omega
  have hprevNe : HalfGap.previousEntry B.brokenAssignment.index.second j
      ≠ none := by
    intro hnone
    have h0 : (B.secondGapLeft j).length = 0 := by
      simp only [secondGapLeft]
      rw [hnone]
      simp
    omega
  obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp hprevNe
  have hp : HalfGap.previousEntry B.brokenAssignment.index.second j =
      some p := by simpa using hp'
  exact B.secondGap_leftConnector_component j p hp hzero hseam

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
