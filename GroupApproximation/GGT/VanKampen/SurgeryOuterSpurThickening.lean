import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingRegions
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening outer spurs into G-cell digons

A section word may backtrack, so the boundary of a diagram can carry a spur: an edge with
the exterior on both sides.  `FaceEdgeDoubling.diagram` doubles an edge of an inner face
only.  This file doubles an edge of the exterior.

Let `w_j` be a dart of the outer traversal `w_0 … w_{n-1}`.  Rebase the traversal at `w_j`
and insert an edge between the corners before and after `w_j` (`EdgeInsertion.splitMap`),
labelled by the label of `w_j`.  The inserted edge closes a digon `none, w_j`, a G-cell of
value one, and the exterior reads the old traversal with the new dart in the place of `w_j`
(`FaceEdgeDoubling.boundary_cellFace_darts`).  The boundary word and the relator cells are
unchanged, so the new diagram is O-equivalent over the same section cuts.  When `α w_j` is on
the exterior too, the spur `w_j, α w_j` is replaced by the new outer dart and `α w_j`, whose
reverses `none` and `w_j` lie on the digon.  No spur is created, so the number of outer spurs
drops by one.

No selected region contains the exterior, so every region of a section family transports with
its face set, weight, target profile and source cell.  The outer arcs change only at `α w_j`,
which lies on no region boundary when its face is the exterior.  Induction on the number of
outer spurs gives `OuterSpurThickeningStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.OuterSpurThickening

open Embedded
open scoped Classical

universe u w v

/-- An **outer spur**: a dart on the exterior whose reverse is also on the exterior. -/
def IsOuterSpur {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (x : Delta.toCombMap.Dart) : Prop :=
  Delta.toCombMap.faceOf x = Delta.outerFace ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) = Delta.outerFace

/-- The number of outer spur darts. -/
noncomputable def outerSpurCount {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (Delta : DiscDiagram.{u, w, v} W) : ℕ :=
  (Finset.univ.filter (IsOuterSpur Delta)).card

/-- **Outer spur thickening.**  A distinguished section family has a distinguished section
family over the same cuts whose diagram is O-equivalent to the old one and has no outer spur.
Its regions correspond bijectively to the old ones, with the same total weight, and every
region keeps its target profile and the index of its source cell. -/
def OuterSpurThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsOuterSpur S'.diagram x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val

end GroupApproximation.GGT.VanKampen.OuterSpurThickening
