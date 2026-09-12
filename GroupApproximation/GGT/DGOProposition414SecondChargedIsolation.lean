import GroupApproximation.GGT.DGOProposition414SecondChargedConnectorSeparation
import GroupApproximation.GGT.DGOProposition414CycleBlocks
import GroupApproximation.GGT.DGOProposition414ChordArcSeamProofWrapped

/-!
# Full auxiliary-cycle isolation of charged wrapped-gap targets

The four opponent blocks exhaust every component start. Separation from each
block has already been transported to chord geodesicity or isolation in the parent polygon;
the component field supplies maximality at the target itself.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A charged wrapped-gap target is isolated in its entire auxiliary cycle,
including against component starts created by the cuts. -/
theorem secondGapChordSource_cycleIsolated
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapChordSources j) :
    IsIsolated D.fam (B.secondGapLocalLabel j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s)))
      (vertex B.firstBase B.chord (B.secondGapChordFinish j)) (B.secondGapCycle j)
      (B.secondGapCut j (B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s))) := by
  refine ⟨⟨_, B.secondGapChordComponentFieldFull j s hs⟩, ?_⟩
  intro q hne hop
  rw [B.secondGapLocalLabel_chord j s hs] at hop ⊢
  have hq : q < (B.secondGapCycle j).length :=
    hop.choose_spec.1.trans_le hop.choose_spec.2.1
  rcases auxiliaryCycleWord_index_cases (B.secondGapLeft j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j))
      (B.secondGapRight j)
      (orientedSegment B.chord (B.secondGapChordStart j) (B.secondGapChordFinish j)) hq with
    hleft | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact B.secondGapChordSource_not_connected_left j s hs hleft hop
  · exact B.secondGapChordSource_not_connected_arc j s hs hr hop
  · exact B.secondGapChordSource_not_connected_right j s hs hr hop
  · exact B.secondGapChordSource_not_connected_chord j s hs hr hne hop

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapChordSource_cycleIsolated
