import GroupApproximation.GGT.DGOProposition414ConnectorAnchors
import GroupApproximation.GGT.DGOOrientedSegmentSeparation

/-!
# Transporting unwanted connector connections to isolated source components

A connector remains in its original source's coset. Connections to another
arc letter contradict isolation in the inherited parent arc. Connections to
an oriented child chord excluding the source's partner contradict geodesicity
of the global chord. Both reductions work at the actual auxiliary-cycle base.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A source coset cannot connect through the child to a distinct same-label
letter in its inherited parent arc. -/
theorem firstGap_not_connected_of_distinct_arc_letter
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstTarget) {i q m z : ℕ}
    (hanchor : (vertex B.firstBase B.firstArc (B.firstTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) i ∈ D.fam (P.label s))
    (hm : m < B.firstArc.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hne : m ≠ B.firstTargetPos s)
    (hletter : (B.firstArc[m]'hm).IsCompOf (P.label s))
    (hlink : (vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) q)⁻¹ *
      vertex B.firstBase B.firstArc z ∈ D.fam (P.label s)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) i q := by
  intro hconn
  have hconnArc : Connected D.fam (P.label s) B.firstBase B.firstArc (B.firstTargetPos s) z := by
    change _ ∈ D.fam (P.label s)
    convert (D.fam (P.label s)).mul_mem ((D.fam (P.label s)).mul_mem hanchor hconn) hlink using 1
    group
  exact hne (eq_of_isolated_singleton_of_connected_letter D B.firstArc_isCutPath.letters
    (B.firstArc_targetComponent hs) (B.firstArc_targetIsolated hs) hm hmz hzm hletter hconnArc)

/-- A source coset cannot connect through the child to a chord block excluding
its geodesic partner edge. -/
theorem firstGap_not_connected_chord_of_source_anchor
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget B.componentPlacement.firstSurvives)
    {i r : ℕ}
    (hanchor : (vertex B.firstBase B.firstArc (B.firstTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) i ∈ D.fam (P.label s))
    (hout : ¬ EdgeBetween (B.firstGapChordStart j) (B.firstGapChordFinish j)
      (B.brokenAssignment.first.partner s))
    (hr : r < (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)).length)
    (hop : IsCompStart (P.label s) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j) i
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length + r) := by
  intro hconn
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := (isCompOf_auxiliaryCycle_chord_iff (P.label s) (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j))
    (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)) r hr hcycle).mp
      (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  apply not_connected_orientedSegment_of_outside_component D B.chord_geodesic
    (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
    (B.firstPartner_chord_isComp s hs) hout hr hletter
  have hpartner := B.firstBrokenSource_arc_partner_mem s hs
  change _ ∈ D.fam (P.label s) at hconn
  rw [vertex_auxiliaryCycle_chord, B.firstGap_prefix_endpoint j] at hconn
  convert (D.fam (P.label s)).mul_mem
    ((D.fam (P.label s)).mul_mem ((D.fam (P.label s)).inv_mem hpartner) hanchor) hconn using 1
  group
  rfl

/-- A source coset cannot connect through the child to a distinct same-label
letter in its inherited parent arc. -/
theorem secondGap_not_connected_of_distinct_arc_letter
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondTarget) {i q m z : ℕ}
    (hanchor : (vertex B.secondBase B.secondArc (B.secondTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) i ∈ D.fam (P.label s))
    (hm : m < B.secondArc.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hne : m ≠ B.secondTargetPos s)
    (hletter : (B.secondArc[m]'hm).IsCompOf (P.label s))
    (hlink : (vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) q)⁻¹ *
      vertex B.secondBase B.secondArc z ∈ D.fam (P.label s)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) i q := by
  intro hconn
  have hconnArc : Connected D.fam (P.label s) B.secondBase B.secondArc (B.secondTargetPos s) z := by
    change _ ∈ D.fam (P.label s)
    convert (D.fam (P.label s)).mul_mem ((D.fam (P.label s)).mul_mem hanchor hconn) hlink using 1
    group
  exact hne (eq_of_isolated_singleton_of_connected_letter D B.secondArc_isCutPath.letters
    (B.secondArc_targetComponent hs) (B.secondArc_targetIsolated hs) hm hmz hzm hletter hconnArc)

/-- A source coset cannot connect through the child to a chord block excluding
its geodesic partner edge. -/
theorem secondGap_not_connected_chord_of_source_anchor
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget B.componentPlacement.secondSurvives)
    {i r : ℕ}
    (hanchor : (vertex B.secondBase B.secondArc (B.secondTargetPos s))⁻¹ *
      vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) i ∈ D.fam (P.label s))
    (hout : ¬ EdgeBetween (B.secondGapChordStart j) (B.secondGapChordFinish j)
      (B.brokenAssignment.second.partner s))
    (hr : r < (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)).length)
    (hop : IsCompStart (P.label s) (B.secondGapCycle j)
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j) i
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length + r) := by
  intro hconn
  obtain ⟨endPos, hcomp⟩ := hop
  have hcycle := hcomp.1.trans_le hcomp.2.1
  have hletter := (isCompOf_auxiliaryCycle_chord_iff (P.label s) (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j))
    (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)) r hr hcycle).mp
      (hcomp.2.2.1 _ le_rfl hcomp.1 hcycle)
  apply not_connected_orientedSegment_of_outside_component D B.chord_geodesic
    (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
    (B.secondPartner_chord_isComp s hs) hout hr hletter
  have hpartner := B.secondBrokenSource_arc_partner_mem s hs
  change _ ∈ D.fam (P.label s) at hconn
  rw [vertex_auxiliaryCycle_chord, B.secondGap_prefix_endpoint j] at hconn
  convert (D.fam (P.label s)).mul_mem
    ((D.fam (P.label s)).mul_mem ((D.fam (P.label s)).inv_mem hpartner) hanchor) hconn using 1
  group
  rfl

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGap_not_connected_of_distinct_arc_letter

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGap_not_connected_chord_of_source_anchor

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGap_not_connected_of_distinct_arc_letter

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGap_not_connected_chord_of_source_anchor
