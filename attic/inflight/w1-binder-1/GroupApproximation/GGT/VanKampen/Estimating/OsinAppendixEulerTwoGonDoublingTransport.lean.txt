import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonCopyRoute
import GroupApproximation.GGT.VanKampen.SurgeryOuterSideThickening
import GroupApproximation.GGT.VanKampen.SurgeryCellSideThickeningPreserves
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningStep
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through one face-edge doubling

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`TwoGonCleanCopyInput` (`Estimating/OsinAppendixEulerTwoGonCopyRoute`) asks for a two-gon of
`phiMapO` on an optimal family whose diagram satisfies the edge conditions.  The closed thickenings
reach such a diagram one face-edge doubling at a time: `OuterSpurThickening`, `OuterCellThickening`,
`OuterSideThickening`, `CellSideThickening`, `CellHairThickening` and `RegionPairThickening`.  This
module states the invariant a two-gon has to keep through one step of each.

Hand model of one step (not a Lean model).
* `FaceEdgeDoubling.dartImage` sends the doubled dart `w_j` to the new dart and embeds every other
  dart.  The doubled face reads its old traversal through `dartImage`, and every other face keeps its
  darts.
* The doubled dart is a spur, outer-cell, outer-side, cell-side, cell-hair or region-pair dart: a
  side dart or an edge between faces of one kind, never the first dart of a source or target arc.  So
  the retained darts of `phiMapO`, the crossings of the component, are carried by `embed`.
* The rotation of `phiMapO` is the first return of the collapsed face rotation.  Around every face
  the retained darts keep their order, and the new digon holds none.  So the faces of `phiMapO`, the
  regions of their darts and the target profiles are carried, and with them `IsTwoGon`, the labels
  and `¬GapAtOHoldsCorner`.
* Face classes gain only the darts of the digon, a G-face, and relator cells correspond through
  `FaceEdgeDoubling.cellMap`; so `¬HoldsCellO` is carried.
* The region holding the doubled face in a region-pair step is carried by
  `FaceEdgeDoubling.Holding.holdingCandidate`, whose boundary darts are the images of the old ones.

* `HasCleanTwoGon`: no loops, no multiple edges, and a two-gon of `phiMapO` with no corner in its gap
  and no relator cell.
* `TwoGonSpurStepStatement`, `TwoGonOuterCellStepStatement`, `TwoGonOuterSideStepStatement`,
  `TwoGonCellSideStepStatement`, `TwoGonCellHairStepStatement`, `TwoGonRegionPairStepStatement`:
  one doubling step of each thickening keeps `HasCleanTwoGon` (named residuals).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A clean two-gon on a family**: no loops, no multiple edges, and a two-gon of `phiMapO` at the
component of an exterior region, with no corner in its gap and no relator cell. -/
def HasCleanTwoGon (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  S.NoLoops ∧ S.NoMultipleEdges ∧
    ∃ a₀ ∈ S.family, a₀.2.target = none ∧
      ∃ (P : RegionCandidate.ExtPhiData S.family
          (RegionCandidate.linkedComponentO S.family a₀))
        (f : (RegionCandidate.phiMapO S.family
          (RegionCandidate.linkedComponentO S.family a₀)).Face),
        (RegionCandidate.phiSubdividedMultigraphO P).IsTwoGon f ∧
          ¬RegionCandidate.GapAtOHoldsCorner cuts S.family
            (RegionCandidate.linkedComponentO S.family a₀) f ∧
          ¬RegionCandidate.HoldsCellO S.family
            (RegionCandidate.linkedComponentO S.family a₀) f

/-- **A clean two-gon through an outer spur doubling** (named residual). -/
def TwoGonSpurStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}, Delta.LeastArea →
    ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hspur : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace),
      HasCleanTwoGon S → HasCleanTwoGon (OuterSpurThickening.sectionFamily S j hlen hspur)

/-- **A clean two-gon through an outer cell doubling** (named residual). -/
def TwoGonOuterCellStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}, Delta.LeastArea →
    ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) ∉ a.1),
      HasCleanTwoGon S →
        HasCleanTwoGon (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid)

/-- **A clean two-gon through an outer side doubling** (named residual). -/
def TwoGonOuterSideStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}, Delta.LeastArea →
    ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
      (htgt : ∀ a ∈ S.family, S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) ∉ a.2.targetArc.darts),
      HasCleanTwoGon S →
        HasCleanTwoGon (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt)

/-- **A clean two-gon through a cell side doubling** (named residual). -/
def TwoGonCellSideStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}, Delta.LeastArea →
    ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
      (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family),
      HasCleanTwoGon S →
        HasCleanTwoGon (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid)

/-- **A clean two-gon through a cell hair doubling** (named residual). -/
def TwoGonCellHairStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}, Delta.LeastArea →
    ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
      (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1),
      HasCleanTwoGon S →
        HasCleanTwoGon (HairOpening.sectionFamily S f j hlen hf havoid)

/-- **A clean two-gon through a region pair doubling** (named residual). -/
def TwoGonRegionPairStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}, Delta.LeastArea →
    ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
      (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
      (T : RegionPairThickening.StepData S.diagram f j S.family),
      HasCleanTwoGon S →
        HasCleanTwoGon (RegionPairThickening.sectionFamily S f j hlen hf T)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.HasCleanTwoGon
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonSpurStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonOuterCellStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonCellSideStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonCellHairStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonRegionPairStepStatement
