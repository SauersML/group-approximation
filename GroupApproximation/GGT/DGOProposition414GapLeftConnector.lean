import GroupApproximation.GGT.DGOProposition414GapRightConnectorWrapped

/-!
# The left connector of a Proposition 4.14 gap child

The connector `e_{j-1}` opening the auxiliary cycle `c_j` is a single
peripheral letter labelled by the preceding broken source `p_{i_{j-1}}`.  Its
predecessor clause is vacuous, so its maximality needs only the letter after
it, which is the first inherited arc letter, or the right connector when the
gap arc is empty, or the head of the child chord when both are empty:

* the first arc letter is the parent letter immediately after `p_{i_{j-1}}`,
  excluded by that parent component's own maximality clause;
* an empty gap arc makes the two adjacent broken sources consecutive one-edge
  components of the parent arc, so their labels differ;
* the third case is DGO's "if `f_j` or `e_j` is connected to a component `x`
  of a side of type (5) … then `y_j` is connected to `x`, contradicting that
  `t` is geodesic", and is named here as `FirstGapLeftConnectorChordSeam`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## The first inherited arc letter -/

/-- The first letter of a nonempty first-half gap arc is the parent letter
just after the preceding broken source, so it does not carry that source's
label. -/
theorem firstGap_arcFirst_not_isCompOf
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (harc : 0 < (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length) :
    ¬ ((arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j))[0]'harc).IsCompOf
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p)) := by
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first p
  have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
  have hcutEnd : B.firstArcCut (B.firstGapFinishSide j) ≤ B.firstArc.length :=
    B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j)
  have harcLen : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length =
      B.firstArcCut (B.firstGapFinishSide j) -
        B.firstArcCut (B.firstGapStartSide j) :=
    length_arcWord B.firstArc B.firstArcCut hcutEnd
  have hstartSide : B.firstGapStartSide j =
      B.firstTargetSide (HalfEntry.entrySource
        B.brokenAssignment.index.first p) + 1 := by
    simp only [firstGapStartSide]
    rw [hp]
  have hcutStart : B.firstArcCut (B.firstGapStartSide j) =
      B.firstTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.first p) + 1 := by
    rw [hstartSide]
    exact (B.firstArcCut_target hpTarget).2
  have hi : 0 < B.firstArcCut (B.firstGapFinishSide j) -
      B.firstArcCut (B.firstGapStartSide j) := by omega
  have hlt : B.firstTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.first p) + 1 < B.firstArc.length := by omega
  intro hletter
  rw [getElem_arcWord B.firstArc B.firstArcCut hcutEnd hi] at hletter
  have hidx : B.firstArcCut (B.firstGapStartSide j) + 0 =
      B.firstTargetPos (HalfEntry.entrySource
        B.brokenAssignment.index.first p) + 1 := by omega
  have hparent : (B.firstArc[B.firstTargetPos (HalfEntry.entrySource
      B.brokenAssignment.index.first p) + 1]'hlt).IsCompOf
      (P.label (HalfEntry.entrySource
        B.brokenAssignment.index.first p)) := by
    rw [← getElem_congr_idx (c := B.firstArc) hidx]
    exact hletter
  exact (B.firstArc_targetComponent hpTarget).2.2.2.2 hlt hparent

/-! ## The residual chord seam at a left connector -/

/-- The chord-seam exclusion for a first-half left connector: when the gap arc
and the right connector are both empty, the head of the child chord does not
carry the preceding broken source's label. -/
def FirstGapLeftConnectorChordSeam
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : Prop :=
  (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length = 0 →
    (B.firstGapRight j).length = 0 →
    ∀ hn : 1 < (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[1]'hn).IsCompOf (B.firstGapLocalLabel j 0)

/-- A nonempty gap arc makes the left-connector chord seam vacuous. -/
theorem firstGapLeftConnectorChordSeam_of_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (harc : 0 < (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)).length) :
    FirstGapLeftConnectorChordSeam B j := by
  intro hA0
  exact absurd hA0 (by omega)

/-- A nonempty right connector makes the left-connector chord seam vacuous. -/
theorem firstGapLeftConnectorChordSeam_of_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hright : 0 < (B.firstGapRight j).length) :
    FirstGapLeftConnectorChordSeam B j := by
  intro _ hR0
  exact absurd hR0 (by omega)

/-- The degenerate empty-cycle model satisfies the left-connector chord
seam. -/
theorem firstGapLeftConnectorChordSeam_of_emptyCycle
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (hcycle : B.firstGapCycle j = []) :
    FirstGapLeftConnectorChordSeam B j := by
  intro _ _ hn
  exact absurd hn (by rw [hcycle]; simp)

/-! ## The successor exclusion for a first-half left connector -/

/-- The letter after a first-half left connector does not carry that
connector's label. -/
theorem firstGap_leftConnector_next_exclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hzero : 0 < (B.firstGapLeft j).length)
    (hseam : FirstGapLeftConnectorChordSeam B j) :
    ∀ hn : 1 < (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[1]'hn).IsCompOf
        (B.firstGapLocalLabel j 0) := by
  classical
  intro hn hletter
  have hone : (B.firstGapLeft j).length = 1 := by
    have hle := B.firstGapLeft_length_le_one j
    omega
  have hlab : B.firstGapLocalLabel j 0 =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first p) :=
    B.firstGapLocalLabel_leftConnector j p hp 0 hzero
  rw [hlab] at hletter
  have hpBroken := HalfEntry.entrySource_mem B.brokenAssignment.index.first p
  have hpTarget := (mem_brokenSet_iff.mp hpBroken).1
  by_cases harc : 0 < (arcWord B.firstArc B.firstArcCut
      (B.firstGapStartSide j) (B.firstGapFinishSide j)).length
  · have hcycleLt : (B.firstGapLeft j).length + 0 <
        (B.firstGapCycle j).length := by omega
    have hgetEq : (B.firstGapCycle j)[1]'hn =
        (B.firstGapCycle j)[(B.firstGapLeft j).length + 0]'hcycleLt :=
      getElem_congr_idx (by omega)
    rw [hgetEq] at hletter
    have hco := (isCompOf_auxiliaryCycle_arc_iff
      (P.label (HalfEntry.entrySource B.brokenAssignment.index.first p))
      (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j)
        (B.firstGapChordFinish j)) 0 harc hcycleLt).mp hletter
    exact B.firstGap_arcFirst_not_isCompOf j p hp harc hco
  · have hA0 : (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)).length = 0 := by omega
    by_cases hright : 0 < (B.firstGapRight j).length
    · have hnxt : HalfGap.nextEntry B.brokenAssignment.index.first j
          ≠ none := by
        intro hnone
        have h0 : (B.firstGapRight j).length = 0 := by
          simp only [firstGapRight]
          rw [hnone]
          simp
        omega
      obtain ⟨e, he'⟩ := Option.ne_none_iff_exists'.mp hnxt
      have he : HalfGap.nextEntry B.brokenAssignment.index.first j =
          some e := by simpa using he'
      have hcycleLt : (B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length + 0 <
          (B.firstGapCycle j).length := by omega
      have hgetEq : (B.firstGapCycle j)[1]'hn =
          (B.firstGapCycle j)[(B.firstGapLeft j).length +
            (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)).length + 0]'hcycleLt :=
        getElem_congr_idx (by omega)
      rw [hgetEq] at hletter
      have hconn := B.firstGap_rightConnector_isCompOf j e he 0 hright hcycleLt
      have hrlab : B.firstGapLocalLabel j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + 0) =
          P.label (HalfEntry.entrySource
            B.brokenAssignment.index.first e) :=
        B.firstGapLocalLabel_rightConnector j e he 0 hright
      rw [hrlab] at hconn
      have hconn' : ((B.firstGapCycle j)[(B.firstGapLeft j).length +
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length + 0]'hcycleLt).IsCompOf
          (P.label (HalfEntry.entrySource
            B.brokenAssignment.index.first e)) := by
        simpa [List.get_eq_getElem] using hconn
      have hEqLabel : P.label (HalfEntry.entrySource
            B.brokenAssignment.index.first p) =
          P.label (HalfEntry.entrySource
            B.brokenAssignment.index.first e) :=
        eq_of_isCompOf_of_isCompOf hletter hconn'
      have heBroken := HalfEntry.entrySource_mem
        B.brokenAssignment.index.first e
      have heTarget := (mem_brokenSet_iff.mp heBroken).1
      have hstartSide : B.firstGapStartSide j =
          B.firstTargetSide (HalfEntry.entrySource
            B.brokenAssignment.index.first p) + 1 := by
        simp only [firstGapStartSide]
        rw [hp]
      have hfinishSide : B.firstGapFinishSide j =
          B.firstTargetSide (HalfEntry.entrySource
            B.brokenAssignment.index.first e) := by
        simp only [firstGapFinishSide]
        rw [he]
      have hcutEnd : B.firstArcCut (B.firstGapFinishSide j) ≤
          B.firstArc.length :=
        B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j)
      have harcLen : (arcWord B.firstArc B.firstArcCut
          (B.firstGapStartSide j) (B.firstGapFinishSide j)).length =
          B.firstArcCut (B.firstGapFinishSide j) -
            B.firstArcCut (B.firstGapStartSide j) :=
        length_arcWord B.firstArc B.firstArcCut hcutEnd
      have hcutStart : B.firstArcCut (B.firstGapStartSide j) =
          B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first p) + 1 := by
        rw [hstartSide]
        exact (B.firstArcCut_target hpTarget).2
      have hcutFinish : B.firstArcCut (B.firstGapFinishSide j) =
          B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first e) := by
        rw [hfinishSide]
        exact (B.firstArcCut_target heTarget).1
      have hposLt : B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first p) <
          B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first e) :=
        HalfGap.pos_entrySource_lt_of_adjacent
          B.brokenAssignment.index.first j hp he
      have hadj : B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first p) + 1 =
          B.firstTargetPos (HalfEntry.entrySource
            B.brokenAssignment.index.first e) := by omega
      exact B.firstTarget_label_ne_of_succ hpTarget heTarget hadj hEqLabel
    · rw [← hlab] at hletter
      exact hseam hA0 (by omega) hn hletter

/-! ## The left connector component -/

/-- A first-half left connector is a maximal one-letter component of its
auxiliary cycle, given the residual chord seam. -/
theorem firstGap_leftConnector_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (p : Fin B.brokenAssignment.index.first.sources.length)
    (hp : HalfGap.previousEntry B.brokenAssignment.index.first j = some p)
    (hzero : 0 < (B.firstGapLeft j).length)
    (hseam : FirstGapLeftConnectorChordSeam B j) :
    IsComp (B.firstGapLocalLabel j 0) (B.firstGapCycle j)
      (B.firstGapCut j 0) (B.firstGapCut j 1) :=
  B.firstGap_leftConnector_cycleComponent j p hp hzero
    (B.firstGap_leftConnector_next_exclusion j p hp hzero hseam)

/-- The `leftComponent` field of `FirstGapComponentFamily`, from the residual
chord seam alone. -/
theorem firstGap_leftComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (r : ℕ) (hr : r < (B.firstGapLeft j).length)
    (hseam : FirstGapLeftConnectorChordSeam B j) :
    IsComp (B.firstGapLocalLabel j r) (B.firstGapCycle j)
      (B.firstGapCut j r) (B.firstGapCut j (r + 1)) := by
  classical
  have hle := B.firstGapLeft_length_le_one j
  have hr0 : r = 0 := by omega
  subst hr0
  have hzero : 0 < (B.firstGapLeft j).length := by omega
  have hprevNe : HalfGap.previousEntry B.brokenAssignment.index.first j
      ≠ none := by
    intro hnone
    have h0 : (B.firstGapLeft j).length = 0 := by
      simp only [firstGapLeft]
      rw [hnone]
      simp
    omega
  obtain ⟨p, hp'⟩ := Option.ne_none_iff_exists'.mp hprevNe
  have hp : HalfGap.previousEntry B.brokenAssignment.index.first j =
      some p := by simpa using hp'
  exact B.firstGap_leftConnector_component j p hp hzero hseam

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
