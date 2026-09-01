import GroupApproximation.GGT.DGOProposition414GapLocalTarget
import GroupApproximation.GGT.DGOProposition414GapClosure

/-!
# Labels and cut edges for canonical gap targets

The arc and chord blocks of a child are disjoint, and each source-to-index map
is injective on the sources assigned to that child.  Hence every generated
local target has a canonical source label.  The same coordinates reflect the
parent distinguished arc sides and cut out literal one-letter edges.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- On one oriented segment, different covered forward chord edges have
different local indices. -/
theorem orientedEdgeIndex_injective {a b x y : ℕ}
    (hx : EdgeBetween a b x) (hy : EdgeBetween a b y)
    (heq : orientedEdgeIndex a b x = orientedEdgeIndex a b y) : x = y := by
  have hx' := hx
  have hy' := hy
  unfold EdgeBetween at hx' hy'
  by_cases hab : a ≤ b
  · have hxf : a ≤ x ∧ x + 1 ≤ b := by omega
    have hyf : a ≤ y ∧ y + 1 ≤ b := by omega
    simp only [orientedEdgeIndex, if_pos hab] at heq
    omega
  · have hxr : b ≤ x ∧ x + 1 ≤ a := by omega
    have hyr : b ≤ y ∧ y + 1 ≤ a := by omega
    simp only [orientedEdgeIndex, if_neg hab] at heq
    omega

namespace BalancedSplitData

theorem firstGapArcSource_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    {s t : ℕ} (hs : s ∈ B.firstGapArcSources j)
    (ht : t ∈ B.firstGapArcSources j)
    (heq : (B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) =
      (B.firstGapLeft j).length +
        (B.firstTargetSide t - B.firstGapStartSide j)) : s = t := by
  have hsData := Finset.mem_filter.mp hs
  have htData := Finset.mem_filter.mp ht
  have hside : B.firstTargetSide s = B.firstTargetSide t := by omega
  apply B.componentPlacement.firstPos_injective hsData.1 htData.1
  change B.firstTargetPos s = B.firstTargetPos t
  rw [← (B.firstArcCut_target hsData.1).1,
    ← (B.firstArcCut_target htData.1).1, hside]

theorem secondGapArcSource_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    {s t : ℕ} (hs : s ∈ B.secondGapArcSources j)
    (ht : t ∈ B.secondGapArcSources j)
    (heq : (B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) =
      (B.secondGapLeft j).length +
        (B.secondTargetSide t - B.secondGapStartSide j)) : s = t := by
  have hsData := Finset.mem_filter.mp hs
  have htData := Finset.mem_filter.mp ht
  have hside : B.secondTargetSide s = B.secondTargetSide t := by omega
  apply B.componentPlacement.secondPos_injective hsData.1 htData.1
  change B.secondTargetPos s = B.secondTargetPos t
  rw [← (B.secondArcCut_target hsData.1).1,
    ← (B.secondArcCut_target htData.1).1, hside]

theorem firstGapChordSource_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    {s t : ℕ} (hs : s ∈ B.firstGapChordSources j)
    (ht : t ∈ B.firstGapChordSources j)
    (heq : B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner s) =
      B.firstGapChordTargetIndex j
        (B.brokenAssignment.second.partner t)) : s = t := by
  have hsData := Finset.mem_filter.mp hs
  have htData := Finset.mem_filter.mp ht
  have hownerS := hsData.2
  have hownerT := htData.2
  have hedgeS := B.secondPartnerFirstGapOwner_edge s hsData.1
  have hedgeT := B.secondPartnerFirstGapOwner_edge t htData.1
  rw [hownerS] at hedgeS
  rw [hownerT] at hedgeT
  have hpartner : B.brokenAssignment.second.partner s =
      B.brokenAssignment.second.partner t := by
    unfold firstGapChordTargetIndex auxiliaryChordTargetIndex at heq
    exact orientedEdgeIndex_injective hedgeS hedgeT (by omega)
  exact B.brokenAssignment.second.partner_injective hsData.1 htData.1 hpartner

theorem secondGapChordSource_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    {s t : ℕ} (hs : s ∈ B.secondGapChordSources j)
    (ht : t ∈ B.secondGapChordSources j)
    (heq : B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner s) =
      B.secondGapChordTargetIndex j
        (B.brokenAssignment.first.partner t)) : s = t := by
  have hsData := Finset.mem_filter.mp hs
  have htData := Finset.mem_filter.mp ht
  have hownerS := hsData.2
  have hownerT := htData.2
  have hedgeS := B.firstPartnerSecondGapOwner_edge s hsData.1
  have hedgeT := B.firstPartnerSecondGapOwner_edge t htData.1
  rw [hownerS] at hedgeS
  rw [hownerT] at hedgeT
  have hpartner : B.brokenAssignment.first.partner s =
      B.brokenAssignment.first.partner t := by
    unfold secondGapChordTargetIndex auxiliaryChordTargetIndex at heq
    exact orientedEdgeIndex_injective hedgeS hedgeT (by omega)
  exact B.brokenAssignment.first.partner_injective hsData.1 htData.1 hpartner

/-- Canonical label dictionary of a first-half gap. -/
noncomputable def firstGapLocalLabel
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) (q : ℕ) : Λ :=
  if q < (B.firstGapLeft j).length then
    match HalfGap.previousEntry B.brokenAssignment.index.first j with
    | none => P.label 0
    | some e => P.label
        (HalfEntry.entrySource B.brokenAssignment.index.first e)
  else if hq : q ∈ B.firstGapArcTarget j then
    P.label (Classical.choose (Finset.mem_image.mp hq))
  else if hq : q ∈ B.firstGapChordTarget j then
    P.label (Classical.choose (Finset.mem_image.mp hq))
  else if q < (B.firstGapLeft j).length +
      (B.firstGapFinishSide j - B.firstGapStartSide j) +
        (B.firstGapRight j).length then
    match HalfGap.nextEntry B.brokenAssignment.index.first j with
    | none => P.label 0
    | some e => P.label
        (HalfEntry.entrySource B.brokenAssignment.index.first e)
  else P.label 0

/-- Canonical label dictionary of a wrapped-half gap. -/
noncomputable def secondGapLocalLabel
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (q : ℕ) : Λ :=
  if q < (B.secondGapLeft j).length then
    match HalfGap.previousEntry B.brokenAssignment.index.second j with
    | none => P.label 0
    | some e => P.label
        (HalfEntry.entrySource B.brokenAssignment.index.second e)
  else if hq : q ∈ B.secondGapArcTarget j then
    P.label (Classical.choose (Finset.mem_image.mp hq))
  else if hq : q ∈ B.secondGapChordTarget j then
    P.label (Classical.choose (Finset.mem_image.mp hq))
  else if q < (B.secondGapLeft j).length +
      (B.secondGapFinishSide j - B.secondGapStartSide j) +
        (B.secondGapRight j).length then
    match HalfGap.nextEntry B.brokenAssignment.index.second j with
    | none => P.label 0
    | some e => P.label
        (HalfEntry.entrySource B.brokenAssignment.index.second e)
  else P.label 0

theorem firstGapLocalLabel_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    B.firstGapLocalLabel j ((B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j)) = P.label s := by
  classical
  let q := (B.firstGapLeft j).length +
    (B.firstTargetSide s - B.firstGapStartSide j)
  have hq : q ∈ B.firstGapArcTarget j := Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hnotLeft : ¬ q < (B.firstGapLeft j).length := by
    dsimp [q]
    omega
  unfold firstGapLocalLabel
  rw [if_neg hnotLeft, dif_pos hq]
  let t := Classical.choose (Finset.mem_image.mp hq)
  have ht := Classical.choose_spec (Finset.mem_image.mp hq)
  congr 1
  exact B.firstGapArcSource_injective j ht.1 hs ht.2

theorem secondGapLocalLabel_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    B.secondGapLocalLabel j ((B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j)) = P.label s := by
  classical
  let q := (B.secondGapLeft j).length +
    (B.secondTargetSide s - B.secondGapStartSide j)
  have hq : q ∈ B.secondGapArcTarget j := Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hnotLeft : ¬ q < (B.secondGapLeft j).length := by
    dsimp [q]
    omega
  unfold secondGapLocalLabel
  rw [if_neg hnotLeft, dif_pos hq]
  let t := Classical.choose (Finset.mem_image.mp hq)
  have ht := Classical.choose_spec (Finset.mem_image.mp hq)
  congr 1
  exact B.secondGapArcSource_injective j ht.1 hs ht.2

private theorem firstGap_arc_chord_disjoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    Disjoint (B.firstGapArcTarget j) (B.firstGapChordTarget j) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqArc hqChord
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hqArc
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hqChord
  have hsRange := (Finset.mem_filter.mp hs).2
  unfold firstGapChordTargetIndex auxiliaryChordTargetIndex at heq
  omega

private theorem secondGap_arc_chord_disjoint
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    Disjoint (B.secondGapArcTarget j) (B.secondGapChordTarget j) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqArc hqChord
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hqArc
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hqChord
  have hsRange := (Finset.mem_filter.mp hs).2
  unfold secondGapChordTargetIndex auxiliaryChordTargetIndex at heq
  omega

theorem firstGapLocalLabel_chord
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) :
    B.firstGapLocalLabel j (B.firstGapChordTargetIndex j
      (B.brokenAssignment.second.partner s)) = P.label s := by
  classical
  let q := B.firstGapChordTargetIndex j
    (B.brokenAssignment.second.partner s)
  have hqChord : q ∈ B.firstGapChordTarget j :=
    Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hqArc : q ∉ B.firstGapArcTarget j := fun h =>
    Finset.disjoint_left.mp (B.firstGap_arc_chord_disjoint j) h hqChord
  have hnotLeft : ¬ q < (B.firstGapLeft j).length := by
    dsimp [q]
    unfold firstGapChordTargetIndex auxiliaryChordTargetIndex
    omega
  unfold firstGapLocalLabel
  rw [if_neg hnotLeft, dif_neg hqArc, dif_pos hqChord]
  let t := Classical.choose (Finset.mem_image.mp hqChord)
  have ht := Classical.choose_spec (Finset.mem_image.mp hqChord)
  congr 1
  exact B.firstGapChordSource_injective j ht.1 hs ht.2

theorem secondGapLocalLabel_chord
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) :
    B.secondGapLocalLabel j (B.secondGapChordTargetIndex j
      (B.brokenAssignment.first.partner s)) = P.label s := by
  classical
  let q := B.secondGapChordTargetIndex j
    (B.brokenAssignment.first.partner s)
  have hqChord : q ∈ B.secondGapChordTarget j :=
    Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hqArc : q ∉ B.secondGapArcTarget j := fun h =>
    Finset.disjoint_left.mp (B.secondGap_arc_chord_disjoint j) h hqChord
  have hnotLeft : ¬ q < (B.secondGapLeft j).length := by
    dsimp [q]
    unfold secondGapChordTargetIndex auxiliaryChordTargetIndex
    omega
  unfold secondGapLocalLabel
  rw [if_neg hnotLeft, dif_neg hqArc, dif_pos hqChord]
  let t := Classical.choose (Finset.mem_image.mp hqChord)
  have ht := Classical.choose_spec (Finset.mem_image.mp hqChord)
  congr 1
  exact B.secondGapChordSource_injective j ht.1 hs ht.2

/-- A left connector in a first-half child carries the label of the broken
source immediately preceding that child. -/
theorem firstGapLocalLabel_leftConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hprev : HalfGap.previousEntry B.brokenAssignment.index.first j = some e)
    (r : ℕ) (hr : r < (B.firstGapLeft j).length) :
    B.firstGapLocalLabel j r =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
  unfold firstGapLocalLabel
  rw [if_pos hr, hprev]

/-- A left connector in a wrapped-half child carries the label of the broken
source immediately preceding that child. -/
theorem secondGapLocalLabel_leftConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hprev : HalfGap.previousEntry B.brokenAssignment.index.second j = some e)
    (r : ℕ) (hr : r < (B.secondGapLeft j).length) :
    B.secondGapLocalLabel j r =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
  unfold secondGapLocalLabel
  rw [if_pos hr, hprev]

/-- A right connector in a first-half child carries the label of the broken
source immediately following that child. -/
theorem firstGapLocalLabel_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (e : Fin B.brokenAssignment.index.first.sources.length)
    (hnext : HalfGap.nextEntry B.brokenAssignment.index.first j = some e)
    (r : ℕ) (hr : r < (B.firstGapRight j).length) :
    B.firstGapLocalLabel j ((B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) + r) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.first e) := by
  classical
  let q := (B.firstGapLeft j).length +
    (B.firstGapFinishSide j - B.firstGapStartSide j) + r
  have hnotLeft : ¬ q < (B.firstGapLeft j).length := by dsimp [q]; omega
  have hnotArc : q ∉ B.firstGapArcTarget j := by
    intro hq
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hq
    have hsRange := (Finset.mem_filter.mp hs).2
    dsimp [q] at heq
    omega
  have hnotChord : q ∉ B.firstGapChordTarget j := by
    intro hq
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hq
    dsimp [q] at heq
    unfold firstGapChordTargetIndex auxiliaryChordTargetIndex at heq
    omega
  have hright : q < (B.firstGapLeft j).length +
      (B.firstGapFinishSide j - B.firstGapStartSide j) +
        (B.firstGapRight j).length := by dsimp [q]; omega
  unfold firstGapLocalLabel
  rw [if_neg hnotLeft, dif_neg hnotArc, dif_neg hnotChord,
    if_pos hright, hnext]

/-- A right connector in a wrapped-half child carries the label of the broken
source immediately following that child. -/
theorem secondGapLocalLabel_rightConnector
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (e : Fin B.brokenAssignment.index.second.sources.length)
    (hnext : HalfGap.nextEntry B.brokenAssignment.index.second j = some e)
    (r : ℕ) (hr : r < (B.secondGapRight j).length) :
    B.secondGapLocalLabel j ((B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) + r) =
      P.label (HalfEntry.entrySource B.brokenAssignment.index.second e) := by
  classical
  let q := (B.secondGapLeft j).length +
    (B.secondGapFinishSide j - B.secondGapStartSide j) + r
  have hnotLeft : ¬ q < (B.secondGapLeft j).length := by dsimp [q]; omega
  have hnotArc : q ∉ B.secondGapArcTarget j := by
    intro hq
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hq
    have hsRange := (Finset.mem_filter.mp hs).2
    dsimp [q] at heq
    omega
  have hnotChord : q ∉ B.secondGapChordTarget j := by
    intro hq
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hq
    dsimp [q] at heq
    unfold secondGapChordTargetIndex auxiliaryChordTargetIndex at heq
    omega
  have hright : q < (B.secondGapLeft j).length +
      (B.secondGapFinishSide j - B.secondGapStartSide j) +
        (B.secondGapRight j).length := by dsimp [q]; omega
  unfold secondGapLocalLabel
  rw [if_neg hnotLeft, dif_neg hnotArc, dif_neg hnotChord,
    if_pos hright, hnext]

/-- Every parent first-arc target lying in a gap is reflected at its shifted
local arc coordinate. -/
theorem firstGap_target_reflect
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    ∀ r : ℕ, r < B.firstGapFinishSide j - B.firstGapStartSide j →
      B.firstGapStartSide j + r ∈ B.firstArcTargetSides →
      (B.firstGapLeft j).length + r ∈ B.firstGapLocalTarget j := by
  classical
  intro r hr ht
  obtain ⟨s, hs, hside⟩ := Finset.mem_image.mp ht
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨s, Finset.mem_filter.mpr ⟨hs, ?_⟩, ?_⟩
  · omega
  · omega

/-- Every parent wrapped-arc target lying in a gap is reflected locally. -/
theorem secondGap_target_reflect
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    ∀ r : ℕ, r < B.secondGapFinishSide j - B.secondGapStartSide j →
      B.secondGapStartSide j + r ∈ B.secondArcTargetSides →
      (B.secondGapLeft j).length + r ∈ B.secondGapLocalTarget j := by
  classical
  intro r hr ht
  obtain ⟨s, hs, hside⟩ := Finset.mem_image.mp ht
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨s, Finset.mem_filter.mpr ⟨hs, ?_⟩, ?_⟩
  · omega
  · omega

theorem firstGapFinishSide_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    B.firstGapFinishSide j ≤ B.secondSide - B.firstSide + 1 := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.first j with
  | none => simp [firstGapFinishSide, hnext]
  | some e =>
      have hmem := HalfEntry.entrySource_mem
        B.brokenAssignment.index.first e
      have htarget := (mem_brokenSet_iff.mp hmem).1
      have hlt := B.firstTargetSide_lt htarget
      simpa only [firstGapFinishSide, hnext] using hlt.le

theorem secondGapFinishSide_le
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    B.secondGapFinishSide j ≤
      (n - B.secondSide) + B.firstSide + 1 := by
  classical
  cases hnext : HalfGap.nextEntry B.brokenAssignment.index.second j with
  | none => simp [secondGapFinishSide, hnext]
  | some e =>
      have hmem := HalfEntry.entrySource_mem
        B.brokenAssignment.index.second e
      have htarget := (mem_brokenSet_iff.mp hmem).1
      have hlt := B.secondTargetSide_lt htarget
      simpa only [secondGapFinishSide, hnext] using hlt.le

/-- Every canonical first-gap local target is a literal one-letter side of
the restricted auxiliary cut. -/
theorem firstGapLocalTarget_edge
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    ∀ q ∈ B.firstGapLocalTarget j,
      auxiliaryCycleCut (B.firstGapLeft j)
          (B.firstGapFinishSide j - B.firstGapStartSide j)
          (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
            B.firstArcCut (B.firstGapStartSide j))
          (B.firstGapRight j) (q + 1) =
        auxiliaryCycleCut (B.firstGapLeft j)
          (B.firstGapFinishSide j - B.firstGapStartSide j)
          (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
            B.firstArcCut (B.firstGapStartSide j))
          (B.firstGapRight j) q + 1 := by
  classical
  intro q hq
  have hside := B.firstGap_side_order j
  have hlast := B.firstGapFinishSide_le j
  let restricted := IsCutPath.arcWord B.firstArc_isCutPath hside hlast
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hsData := Finset.mem_filter.mp hs
    let r := B.firstTargetSide s - B.firstGapStartSide j
    have hr : r < B.firstGapFinishSide j - B.firstGapStartSide j := by
      dsimp [r]
      omega
    have hrEq : B.firstGapStartSide j + r = B.firstTargetSide s := by
      dsimp [r]
      omega
    have hcut := B.firstArcCut_target hsData.1
    have hbase : B.firstArcCut (B.firstGapStartSide j) ≤
        B.firstArcCut (B.firstTargetSide s) :=
      B.firstArc_isCutPath.cut.mono_le (by omega)
    have hc0 := auxiliaryCycleCut_arc (B.firstGapLeft j)
      (B.firstGapRight j) restricted.cut (r := r) hr.le
    have hc1 := auxiliaryCycleCut_arc (B.firstGapLeft j)
      (B.firstGapRight j) restricted.cut (r := r + 1)
      (Nat.succ_le_iff.mpr hr)
    change auxiliaryCycleCut (B.firstGapLeft j)
        (B.firstGapFinishSide j - B.firstGapStartSide j)
        (fun x => B.firstArcCut (B.firstGapStartSide j + x) -
          B.firstArcCut (B.firstGapStartSide j))
        (B.firstGapRight j)
        ((B.firstGapLeft j).length + r + 1) = _
    rw [show (B.firstGapLeft j).length + r + 1 =
        (B.firstGapLeft j).length + (r + 1) by omega,
      hc1, hc0]
    have hrSucc : B.firstGapStartSide j + (r + 1) =
        B.firstTargetSide s + 1 := by omega
    rw [hrEq, hrSucc, hcut.1, hcut.2]
    omega
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    let r := orientedEdgeIndex (B.firstGapChordStart j)
      (B.firstGapChordFinish j) (B.brokenAssignment.second.partner s)
    have hc0 := auxiliaryCycleCut_chord (B.firstGapLeft j)
      (B.firstGapRight j) restricted.cut (r := r)
    have hc1 := auxiliaryCycleCut_chord (B.firstGapLeft j)
      (B.firstGapRight j) restricted.cut (r := r + 1)
    unfold firstGapChordTargetIndex auxiliaryChordTargetIndex
    change auxiliaryCycleCut (B.firstGapLeft j)
        (B.firstGapFinishSide j - B.firstGapStartSide j)
        (fun x => B.firstArcCut (B.firstGapStartSide j + x) -
          B.firstArcCut (B.firstGapStartSide j))
        (B.firstGapRight j)
        ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) +
          (B.firstGapRight j).length + r + 1) = _
    rw [show (B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) +
          (B.firstGapRight j).length + r + 1 =
        (B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) +
          (B.firstGapRight j).length + (r + 1) by omega,
      hc1, hc0]
    omega

/-- Every canonical wrapped-gap local target is a one-letter side. -/
theorem secondGapLocalTarget_edge
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    ∀ q ∈ B.secondGapLocalTarget j,
      auxiliaryCycleCut (B.secondGapLeft j)
          (B.secondGapFinishSide j - B.secondGapStartSide j)
          (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
            B.secondArcCut (B.secondGapStartSide j))
          (B.secondGapRight j) (q + 1) =
        auxiliaryCycleCut (B.secondGapLeft j)
          (B.secondGapFinishSide j - B.secondGapStartSide j)
          (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
            B.secondArcCut (B.secondGapStartSide j))
          (B.secondGapRight j) q + 1 := by
  classical
  intro q hq
  have hside := B.secondGap_side_order j
  have hlast := B.secondGapFinishSide_le j
  let restricted := IsCutPath.arcWord B.secondArc_isCutPath hside hlast
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hsData := Finset.mem_filter.mp hs
    let r := B.secondTargetSide s - B.secondGapStartSide j
    have hr : r < B.secondGapFinishSide j - B.secondGapStartSide j := by
      dsimp [r]
      omega
    have hrEq : B.secondGapStartSide j + r = B.secondTargetSide s := by
      dsimp [r]
      omega
    have hcut := B.secondArcCut_target hsData.1
    have hbase : B.secondArcCut (B.secondGapStartSide j) ≤
        B.secondArcCut (B.secondTargetSide s) :=
      B.secondArc_isCutPath.cut.mono_le (by omega)
    have hc0 := auxiliaryCycleCut_arc (B.secondGapLeft j)
      (B.secondGapRight j) restricted.cut (r := r) hr.le
    have hc1 := auxiliaryCycleCut_arc (B.secondGapLeft j)
      (B.secondGapRight j) restricted.cut (r := r + 1)
      (Nat.succ_le_iff.mpr hr)
    change auxiliaryCycleCut (B.secondGapLeft j)
        (B.secondGapFinishSide j - B.secondGapStartSide j)
        (fun x => B.secondArcCut (B.secondGapStartSide j + x) -
          B.secondArcCut (B.secondGapStartSide j))
        (B.secondGapRight j)
        ((B.secondGapLeft j).length + r + 1) = _
    rw [show (B.secondGapLeft j).length + r + 1 =
        (B.secondGapLeft j).length + (r + 1) by omega,
      hc1, hc0]
    have hrSucc : B.secondGapStartSide j + (r + 1) =
        B.secondTargetSide s + 1 := by omega
    rw [hrEq, hrSucc, hcut.1, hcut.2]
    omega
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    let r := orientedEdgeIndex (B.secondGapChordStart j)
      (B.secondGapChordFinish j) (B.brokenAssignment.first.partner s)
    have hc0 := auxiliaryCycleCut_chord (B.secondGapLeft j)
      (B.secondGapRight j) restricted.cut (r := r)
    have hc1 := auxiliaryCycleCut_chord (B.secondGapLeft j)
      (B.secondGapRight j) restricted.cut (r := r + 1)
    unfold secondGapChordTargetIndex auxiliaryChordTargetIndex
    change auxiliaryCycleCut (B.secondGapLeft j)
        (B.secondGapFinishSide j - B.secondGapStartSide j)
        (fun x => B.secondArcCut (B.secondGapStartSide j + x) -
          B.secondArcCut (B.secondGapStartSide j))
        (B.secondGapRight j)
        ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) +
          (B.secondGapRight j).length + r + 1) = _
    rw [show (B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) +
          (B.secondGapRight j).length + r + 1 =
        (B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) +
          (B.secondGapRight j).length + (r + 1) by omega,
      hc1, hc0]
    omega

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
