import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellKeptCellNoncrossing
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# A relator cell on the side of the cell pocket walk, from a following boundary cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`.  If `Γ_1` kept no
relator cell, merging the two regions would contradict the extremality of the family.

`CellPocketWalkSideRelatorCellStatement` (`Estimating/OsinPocketMultipleEdgeCopy`) is a named
residual of the binder-5 route, consumed by `multipleEdgePocketRegionCopyInput_of_pinch`.  Its data
are the clean walk data of `CellPocketWalk.exists_clean_of_copy`: a least-area diagram, distinct
regions joining distinct cells under the edge conditions, and their cell pocket walk, a nonempty
closed walk with no repeated dart and no dart together with its reverse.
- `CellPocketWalkColour.walk_orient` orients the walk, so it is noncrossing
  (`ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient`).
- The exterior face is off its side by `CellPocketWalkOuterOffSideStatement`.
- `GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingCellWalk_of_leastArea`
  (`Estimating/OsinPocketCellKeptCellNoncrossing`) then gives a relator cell on the side, once the
  outer or the inner cycle of the walk follows its boundary.
No producer of the following clause is on main for cell pocket walks.  On the lake map the inner
cycle follows and the outer cycle does not
(`OsinPocketCellKeptCellNoncrossing.multipleEdgeLakeInnerBranch`), so the clause is stated as a
disjunction.

* `CellPocketWalkEitherFollowsStatement`: with the same data, the outer cycle or the inner cycle of
  the noncrossing walk follows its boundary (named residual).
* `cellPocketWalkSideRelatorCell_of_eitherFollows`: `CellPocketWalkSideRelatorCellStatement` from
  `CellPocketWalkOuterOffSideStatement` and `CellPocketWalkEitherFollowsStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

/-- **The noncrossing cell pocket walk has a following boundary cycle** (named residual of binder 5),
with the data of `CellPocketWalkOuterOffSideStatement`: when the cell pocket walk of two distinct
regions joining distinct cells under the edge conditions is noncrossing, its outer cycle or its inner
cycle follows its boundary. -/
def CellPocketWalkEitherFollowsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord},
    Delta.LeastArea →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          CellPocketWalk.CopyClean a b i j →
          ∀ K : CellPocketWalk D eps S.diagram i j,
            K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
            (∃ G₁ : CyclicArc (cellDarts S.diagram i),
              K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
            (∃ G₂ : CyclicArc (cellDarts S.diagram j),
              K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
            ∀ hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk,
              (hw.outerCycle S.diagram.planar).FollowsBoundary ∨
                (hw.innerCycle S.diagram.planar).FollowsBoundary

/-- **A relator cell on the side of the cell pocket walk, from a following boundary cycle.**  The
walk is noncrossing by its orientation, the exterior face is off its side by
`CellPocketWalkOuterOffSideStatement`, one of its boundary cycles follows by
`CellPocketWalkEitherFollowsStatement`, and least area passes from `Δ` to the optimal diagram.  So
the kept cell of a noncrossing cell pocket walk lies on its side. -/
theorem cellPocketWalkSideRelatorCell_of_eitherFollows
    (hout : CellPocketWalkOuterOffSideStatement.{u, w, v})
    (hfollow : CellPocketWalkEitherFollowsStatement.{u, w, v}) :
    CellPocketWalkSideRelatorCellStatement.{u, w, v} := by
  intro G _ Lambda W D eps lambda c Delta cuts hlea S i j a b ha hb hab hij hai hbi hclean K
    hfirst hsecond h₁ h₂ hne hchain hcloses hnodup halpha
  have hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk :=
    ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient S.diagram.planar hne hnodup halpha
      hchain hcloses
      (fun _ hcol => CellPocketWalkColour.walk_orient S.toRealizedSectionFamily ha hb hab hai hbi
        K hfirst hsecond h₁ h₂ hcol)
  exact S.exists_kept_of_noncrossingCellWalk_of_leastArea ha hb hab hij hai hbi K hfirst hsecond
    h₁ (OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea) hw
    (hout hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hne hchain hcloses hnodup
      halpha)
    (hfollow hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkEitherFollowsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketWalkSideRelatorCell_of_eitherFollows
