import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through a cell hair doubling

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellHairStepStatement` (the cell-hair step of the
two-gon clean copy, Osin arXiv:math/0411039v3, Lemma 9.7(b), feeding Lemma 4.4; infrastructure for
`thm:hull`, non_mf_groups_exist.tex ~2121).

Mathematical proof.  The hair doubling `HairOpening.sectionFamily S f j hlen hf havoid` doubles the
dart `w = FaceEdgeDoubling.dart S.diagram f j` of an inner face `f`, and carries every region `r`
of the family, which avoids `f` and the face across `w`.  Such a region never uses `w` in a
contiguity arc: the reverse of a source-arc dart lies on the boundary cycle of `r`, hence on a face
of `r`, which would be the face across `w`; a target-arc dart or its reverse lies on the boundary
cycle, hence on `f` or on the face across `w` (`FaceEdgeDoubling.dart_not_mem_sourceArc`,
`FaceEdgeDoubling.dart_not_mem_targetArc`).  So the family satisfies the arc-avoidance hypothesis
of the cell side doubling (`hairFamilyArcAvoid`).  The two surgeries build the same diagram, and each
carried region has the same face set, cells and arcs (`contiguityGeometry` and
`contiguityGeometryOfArcs` have the same data fields), so the two section families coincide
(`hairSectionFamily_eq`, by definitional unfolding).  The step is then the cell-side step
`GreendlingerLeaf.P05CellSide.proof`.
-/

namespace GroupApproximation.Full.GL06b

open GroupApproximation.GGT.VanKampen

universe u w v

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A family avoiding `f` and the face across `w` uses `w` in no contiguity arc** (Osin
Lemma 9.7(b), cell-hair step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem hairFamilyArcAvoid
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family :=
  fun a ha =>
    ⟨(havoid a ha).1,
      FaceEdgeDoubling.dart_not_mem_sourceArc S.diagram f j a.2 (havoid a ha).2,
      FaceEdgeDoubling.dart_not_mem_targetArc S.diagram f j a.2 (havoid a ha).1 (havoid a ha).2⟩

/-- **The hair doubling is the cell side doubling of the same edge** (Osin Lemma 9.7(b),
cell-hair step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem hairSectionFamily_eq
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    HairOpening.sectionFamily S f j hlen hf havoid =
      CellSideThickening.sectionFamilyOfArcs S f j hlen hf (hairFamilyArcAvoid S f j havoid) :=
  rfl

end Family

/-- **A clean two-gon through a cell hair doubling** (Osin Lemma 9.7(b), cell-hair step of the
two-gon clean copy; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem twoGonCellHairStep : TwoGonCellHairStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S f j hlen hf havoid h
  rw [hairSectionFamily_eq S f j hlen hf havoid]
  exact GreendlingerLeaf.P05CellSide.proof hlea S f j hlen hf (hairFamilyArcAvoid S f j havoid) h

end GroupApproximation.Full.GL06b

#audit_axioms GroupApproximation.Full.GL06b.hairSectionFamily_eq
#audit_axioms GroupApproximation.Full.GL06b.twoGonCellHairStep
