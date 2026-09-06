import GroupApproximation.GGT.DGOProposition414FirstChargedConnectorSeparation
import GroupApproximation.GGT.DGOProposition414CycleBlocks
import GroupApproximation.GGT.DGOProposition414ArcChordSeamProofWrapped

/-!
# Full auxiliary-cycle isolation of charged first-gap targets

The four opponent blocks exhaust every component start. Separation from each
block has already been transported to chord geodesicity or isolation in the parent polygon;
the component field supplies maximality at the target itself.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A charged first-gap target is isolated in its entire auxiliary cycle,
including against component starts created by the cuts. -/
theorem firstGapChordSource_cycleIsolated
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapChordSources j) :
    IsIsolated D.fam (B.firstGapLocalLabel j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s)))
      (vertex B.firstBase B.chord (B.firstGapChordFinish j)) (B.firstGapCycle j)
      (B.firstGapCut j (B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s))) := by
  refine ⟨⟨_, B.firstGapChordComponentFieldFull j s hs⟩, ?_⟩
  intro q hne hop
  rw [B.firstGapLocalLabel_chord j s hs] at hop ⊢
  have hq : q < (B.firstGapCycle j).length :=
    hop.choose_spec.1.trans_le hop.choose_spec.2.1
  rcases auxiliaryCycleWord_index_cases (B.firstGapLeft j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j))
      (B.firstGapRight j)
      (orientedSegment B.chord (B.firstGapChordStart j) (B.firstGapChordFinish j)) hq with
    hleft | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact B.firstGapChordSource_not_connected_left j s hs hleft hop
  · exact B.firstGapChordSource_not_connected_arc j s hs hr hop
  · exact B.firstGapChordSource_not_connected_right j s hs hr hop
  · exact B.firstGapChordSource_not_connected_chord j s hs hr hne hop

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapChordSource_cycleIsolated
