import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellSideRelatorCellEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-interleaving passages of the pocket walks

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The kept relator cell of a pocket comes from the pocket region of its walk, built from the Euler
equalities of the two reclosings (`PocketRegion.ofNoncrossingClosedWalkEuler`).  The named residuals
of those equalities are `SectionPocketWalkEulerStatement` (`Estimating/OsinPocketKeptCellSection`)
for the walk of two exterior regions of one cell to one section, and `CellPocketWalkEulerStatement`
(`Estimating/OsinPocketCellSideRelatorCellEuler`) for the walk of two regions joining two cells.
Both reclosings of a noncrossing closed walk whose passages do not interleave keep the Euler
characteristic, once the vertex bound `NoninterleavingVertexCountStatement` holds
(`NoncrossingClosedWalkEulerNoninterleaving`).  So each Euler residual reduces to the
non-interleaving of the passages of its walk.

* `SectionPocketWalkNoninterleavingStatement`: with the data of `SectionPocketWalkEulerStatement`,
  the passages of the noncrossing pocket walk do not interleave (named residual).
* `CellPocketWalkNoninterleavingStatement`: with the data of `CellPocketEulerForOrder`, the same for
  the cell pocket walk (named residual).
* `sectionPocketWalkEuler_of_noninterleaving`, `cellPocketWalkEuler_of_noninterleaving`: the Euler
  residuals from the vertex bound and non-interleaving.
* `sectionPocketKeptCell_of_noninterleaving`: `SectionPocketKeptCellStatement` from the two.

Where non-interleaving comes from.  Every joint `d → next d` of a pocket walk is of one of two kinds.
* A boundary step of one of the two regions: a joint inside a side, or a corner.  Rotating from
  `alpha d` to `next d`, the darts passed are internal to the region, so none is a walk dart or the
  reversal of one.
* A face step of a cell arc read backwards, or of the arc of `∂Δ`: `sigma (next d) = alpha d`, so
  rotating from `alpha d` passes every other dart at the vertex before `next d`.
In either case the passage of any other walk dart at that vertex lies wholly on one side of the
passage of `d`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

/-- **The passages of the section pocket walk do not interleave** (named residual).  On a least-area
diagram, the noncrossing pocket walk `s_1 t_1 s_2 t_2` of two distinct exterior regions of one cell
to one section, in the shape of `PocketWalk.exists_of_exteriorAt` and satisfying the edge conditions,
has non-interleaving passages. -/
def SectionPocketWalkNoninterleavingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    S.diagram.LeastArea →
      ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count)
        (x y : RegionCandidate D eps S.diagram),
        x ∈ RegionCandidate.exteriorAt S.family i → y ∈ RegionCandidate.exteriorAt S.family i →
          x ≠ y → RegionCandidate.TargetsSectionIndex cuts j x →
            RegionCandidate.TargetsSectionIndex cuts j y →
              ∀ K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
                K.source = i → K.firstSide = y.2.leftSide → K.secondSide = x.2.rightSide →
                  (∃ Gap : CyclicArc (cellDarts S.diagram i),
                    K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++
                      y.2.sourceArc.darts) →
                    K.targetArc.start.1 = x.2.targetArc.start.1 →
                      K.targetArc.start.1 + K.targetArc.length =
                          y.2.targetArc.start.1 + y.2.targetArc.length →
                        K.CopyClean x y →
                          IsNoncrossingClosedWalk S.diagram.toCombMap K.walk →
                            PassagesNoninterleaving S.diagram.toCombMap K.walk

/-- **The passages of the cell pocket walk do not interleave** (named residual).  For distinct
selected regions of an optimal family over a least-area diagram joining distinct cells, in every
order, the noncrossing clean cell pocket walk has non-interleaving passages. -/
def CellPocketWalkNoninterleavingStatement : Prop :=
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
            IsNoncrossingClosedWalk S.diagram.toCombMap K.walk →
              PassagesNoninterleaving S.diagram.toCombMap K.walk

/-- **The Euler equalities of the section pocket walk, from non-interleaving.** -/
theorem sectionPocketWalkEuler_of_noninterleaving
    (hcount : NoninterleavingVertexCountStatement.{v})
    (hni : SectionPocketWalkNoninterleavingStatement.{u, w, v}) :
    SectionPocketWalkEulerStatement.{u, w, v} := by
  intro G _ Lambda D lambda c eps W Delta cuts S hlea i j x y hx hy hxy hjx hjy K hsource hfirst
    hsecond hgap hstart hend hclean hw
  exact hw.eulers_of_noninterleaving hcount S.diagram.planar
    (hni D lambda c eps W Delta cuts S hlea i j x y hx hy hxy hjx hjy K hsource hfirst hsecond hgap
      hstart hend hclean hw)

/-- **The Euler equalities of the cell pocket walk, from non-interleaving.** -/
theorem cellPocketWalkEuler_of_noninterleaving
    (hcount : NoninterleavingVertexCountStatement.{v})
    (hni : CellPocketWalkNoninterleavingStatement.{u, w, v}) :
    CellPocketWalkEulerStatement.{u, w, v} := by
  intro G _ Lambda W D eps lambda c Delta cuts hlea S i j a b ha hb hab hij hai hbi hclean K hfirst
    hsecond h₁ h₂ hw
  exact hw.eulers_of_noninterleaving hcount S.diagram.planar
    (hni hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw)

/-- **The kept cell of the section pocket, from the vertex bound and non-interleaving.** -/
theorem sectionPocketKeptCell_of_noninterleaving
    (hcount : NoninterleavingVertexCountStatement.{v})
    (hni : SectionPocketWalkNoninterleavingStatement.{u, w, v}) :
    SectionPocketKeptCellStatement.{u, w, v} :=
  sectionPocketKeptCell_of_euler (sectionPocketWalkEuler_of_noninterleaving hcount hni)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketWalkNoninterleavingStatement
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkNoninterleavingStatement
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketWalkEuler_of_noninterleaving
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketWalkEuler_of_noninterleaving
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketKeptCell_of_noninterleaving
