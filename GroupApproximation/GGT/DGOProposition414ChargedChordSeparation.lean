import GroupApproximation.GGT.DGOOrientedComponentCoset

/-!
# Separation of charged targets from the rest of the child chord

The auxiliary cut is the oriented partner-edge position plus the three preceding
block lengths. Exact vertex transport reduces separation within the chord to
isolation of that singleton in the geodesic oriented segment.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The charged target is read at its oriented partner-edge vertex. -/
theorem firstGapChordSource_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) :
    vertex (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s))) =
      vertex (vertex B.firstBase B.chord (B.firstGapChordStart j))
        (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j))
        (orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s)) := by
  have hcut : B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s)) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + (B.firstGapRight j).length +
        (orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s)) := B.firstGapChordSource_auxiliaryCut j s
  rw [hcut, vertex_auxiliaryCycle_chord, B.firstGap_prefix_endpoint j]

/-- A charged target cannot connect to a different component start in the
chord block of its auxiliary cycle. -/
theorem firstGapChordSource_not_connected_chord
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)).length)
    (hne : (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + (B.firstGapRight j).length + r ≠
      B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s)))
    (hop : IsCompStart (P.label s) (B.firstGapCycle j)
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + (B.firstGapRight j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s)))
      ((B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + (B.firstGapRight j).length + r) := by
  have hcut : B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s)) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + (B.firstGapRight j).length +
        (orientedEdgeIndex (B.firstGapChordStart j) (B.firstGapChordFinish j)
          (B.brokenAssignment.second.partner s)) := B.firstGapChordSource_auxiliaryCut j s
  rw [hcut] at hne ⊢
  have hiso := B.firstGapChordSource_segmentIsolated j s hs
  have hgeo := isGeodesicWord_orientedSegment D hsymm B.chord_geodesic
    (B.firstGapChordStart_le j) (B.firstGapChordFinish_le j)
  apply not_connected_auxiliaryCycle_chord_of_isolated D _ _ _ _ _ hgeo.1
    (B.firstGapChordSource_segmentComponent j s hs) ?_ hr (by omega) hop
  rwa [B.firstGap_prefix_endpoint j]

/-- The charged target is read at its oriented partner-edge vertex. -/
theorem secondGapChordSource_vertex
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) :
    vertex (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s))) =
      vertex (vertex B.firstBase B.chord (B.secondGapChordStart j))
        (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j))
        (orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s)) := by
  have hcut : B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s)) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + (B.secondGapRight j).length +
        (orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s)) := B.secondGapChordSource_auxiliaryCut j s
  rw [hcut, vertex_auxiliaryCycle_chord, B.secondGap_prefix_endpoint j]

/-- A charged target cannot connect to a different component start in the
chord block of its auxiliary cycle. -/
theorem secondGapChordSource_not_connected_chord
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) {r : ℕ}
    (hr : r < (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)).length)
    (hne : (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + (B.secondGapRight j).length + r ≠
      B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s)))
    (hop : IsCompStart (P.label s) (B.secondGapCycle j)
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + (B.secondGapRight j).length + r)) :
    ¬ Connected D.fam (P.label s)
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s)))
      ((B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + (B.secondGapRight j).length + r) := by
  have hcut : B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s)) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + (B.secondGapRight j).length +
        (orientedEdgeIndex (B.secondGapChordStart j) (B.secondGapChordFinish j)
          (B.brokenAssignment.first.partner s)) := B.secondGapChordSource_auxiliaryCut j s
  rw [hcut] at hne ⊢
  have hiso := B.secondGapChordSource_segmentIsolated j s hs
  have hgeo := isGeodesicWord_orientedSegment D hsymm B.chord_geodesic
    (B.secondGapChordStart_le j) (B.secondGapChordFinish_le j)
  apply not_connected_auxiliaryCycle_chord_of_isolated D _ _ _ _ _ hgeo.1
    (B.secondGapChordSource_segmentComponent j s hs) ?_ hr (by omega) hop
  rwa [B.secondGap_prefix_endpoint j]

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_vertex

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_not_connected_chord

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_vertex

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_not_connected_chord
