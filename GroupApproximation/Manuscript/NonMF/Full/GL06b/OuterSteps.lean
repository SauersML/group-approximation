import GroupApproximation.Manuscript.NonMF.Full.GL06b.OuterSideRotation
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through the outer doublings

Targets: `GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement`,
`TwoGonOuterCellStepStatement` and `TwoGonSpurStepStatement` (the outer steps of the two-gon clean
copy, Osin arXiv:math/0411039v3, Lemma 9.7(b), feeding Lemma 4.4; infrastructure for `thm:hull`,
non_mf_groups_exist.tex ~2121).

Mathematical proof.  The outer side doubling carries the family along
`OuterDoublingTransport.regionFamilyEmbedding` (`outerSideTransport`), and carries `Φ'_M` at every
component (`outerSide_phiTransportAt`); so a clean two-gon is carried
(`GreendlingerLeaf.P05CellSide.hasCleanTwoGon_of_transport`).  An outer cell doubling whose family
avoids the face across `w_j` is the outer side doubling of the same edge: such a family never uses
`alpha w_j` in a target arc (`OuterDoublingTransport.not_mem_targetArc_of_avoid`), the two
surgeries build the same diagram, and each carried region has the same face set, cells and arcs
(the two `contiguityGeometry`s have the same data fields), so the section families coincide by
definitional unfolding (`outerCellSectionFamily_eq`).  An outer spur doubling is the outer cell
doubling of the same edge, since the face across a spur is the outer face, which lies in no region
(`OuterSpurThickening.spur_avoid`, `spurSectionFamily_eq`).
-/

namespace GroupApproximation.Full.GL06b

open GroupApproximation.GGT.VanKampen

universe u w v

/-- **A clean two-gon through an outer side doubling** (Osin Lemma 9.7(b), outer-side step of the
two-gon clean copy; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem twoGonOuterSideStep : TwoGonOuterSideStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S j hlen htgt h
  exact GreendlingerLeaf.P05CellSide.hasCleanTwoGon_of_transport hlea
    (outerSideTransport S j hlen htgt) (fun a₀ => outerSide_phiTransportAt S j hlen htgt a₀) h

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The outer cell doubling is the outer side doubling of the same edge** (Osin Lemma 9.7(b),
outer-cell step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerCellSectionFamily_eq
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) ∉ a.1) :
    OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid =
      OuterSideThickening.sectionFamilyOfTransport S j hlen
        (OuterDoublingTransport.not_mem_targetArc_of_avoid S.diagram j S.family havoid) :=
  rfl

/-- **The outer spur doubling is the outer cell doubling of the same edge** (Osin Lemma 9.7(b),
spur step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem spurSectionFamily_eq
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hspur : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace) :
    OuterSpurThickening.sectionFamily S j hlen hspur =
      OuterCellThickening.sectionFamilyOfAvoid S j hlen
        (OuterSpurThickening.spur_avoid S.diagram j hspur S.family) :=
  rfl

end Family

/-- **A clean two-gon through an outer cell doubling** (Osin Lemma 9.7(b), outer-cell step of the
two-gon clean copy; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem twoGonOuterCellStep : TwoGonOuterCellStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S j hlen havoid h
  rw [outerCellSectionFamily_eq S j hlen havoid]
  exact twoGonOuterSideStep hlea S j hlen
    (OuterDoublingTransport.not_mem_targetArc_of_avoid S.diagram j S.family havoid) h

/-- **A clean two-gon through an outer spur doubling** (Osin Lemma 9.7(b), spur step of the
two-gon clean copy; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem twoGonSpurStep : TwoGonSpurStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S j hlen hspur h
  rw [spurSectionFamily_eq S j hlen hspur]
  exact twoGonOuterCellStep hlea S j hlen
    (OuterSpurThickening.spur_avoid S.diagram j hspur S.family) h

end GroupApproximation.Full.GL06b

#audit_axioms GroupApproximation.Full.GL06b.twoGonOuterSideStep
#audit_axioms GroupApproximation.Full.GL06b.outerCellSectionFamily_eq
#audit_axioms GroupApproximation.Full.GL06b.spurSectionFamily_eq
#audit_axioms GroupApproximation.Full.GL06b.twoGonOuterCellStep
#audit_axioms GroupApproximation.Full.GL06b.twoGonSpurStep
