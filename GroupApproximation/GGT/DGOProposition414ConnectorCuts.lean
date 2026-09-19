import GroupApproximation.GGT.DGOProposition414ConnectorAnchors

/-!
# Exact connector cuts in the auxiliary cycles

Connector sides have one letter per side; the right block begins after the
whole inherited arc, whose number of sides need not equal its word length.
-/

namespace GroupApproximation.GGT.DGOProposition414.BalancedSplitData

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The left-connector side cut is its word position. -/
theorem firstGapCut_left
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    {r : ℕ} (hr : r ≤ (B.firstGapLeft j).length) : B.firstGapCut j r = r :=
  auxiliaryCycleCut_left (B.firstGapLeft j) (B.firstGapRight j)
    (B.firstGapFinishSide j - B.firstGapStartSide j)
    (fun r => B.firstArcCut (B.firstGapStartSide j + r) - B.firstArcCut (B.firstGapStartSide j)) hr

/-- The right-connector cut is shifted by the inherited arc's word length. -/
theorem firstGapCut_right
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    {r : ℕ} (hr : r ≤ (B.firstGapRight j).length) :
    B.firstGapCut j ((B.firstGapLeft j).length + (B.firstGapFinishSide j - B.firstGapStartSide j) + r) =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j) (B.firstGapFinishSide j)).length + r := by
  exact auxiliaryCycleCut_right (B.firstGapLeft j) (B.firstGapRight j)
    (IsCutPath.arcWord B.firstArc_isCutPath (B.firstGap_side_order j) (B.firstGapFinishSide_le j)).cut hr

/-- The left-connector side cut is its word position. -/
theorem secondGapCut_left
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    {r : ℕ} (hr : r ≤ (B.secondGapLeft j).length) : B.secondGapCut j r = r :=
  auxiliaryCycleCut_left (B.secondGapLeft j) (B.secondGapRight j)
    (B.secondGapFinishSide j - B.secondGapStartSide j)
    (fun r => B.secondArcCut (B.secondGapStartSide j + r) - B.secondArcCut (B.secondGapStartSide j)) hr

/-- The right-connector cut is shifted by the inherited arc's word length. -/
theorem secondGapCut_right
    {D : RelGenSet G Lambda} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n} (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    {r : ℕ} (hr : r ≤ (B.secondGapRight j).length) :
    B.secondGapCut j ((B.secondGapLeft j).length + (B.secondGapFinishSide j - B.secondGapStartSide j) + r) =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j) (B.secondGapFinishSide j)).length + r := by
  exact auxiliaryCycleCut_right (B.secondGapLeft j) (B.secondGapRight j)
    (IsCutPath.arcWord B.secondArc_isCutPath (B.secondGap_side_order j) (B.secondGapFinishSide_le j)).cut hr

end GroupApproximation.GGT.DGOProposition414.BalancedSplitData

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapCut_left

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.firstGapCut_right

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapCut_left

#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.secondGapCut_right
