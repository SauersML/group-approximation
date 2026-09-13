import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening relator-face edges across region sides: the statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1, s_2` are side arcs of contiguity subdiagrams of the
cell `Π`.

The pocket walk of two exterior regions `x`, `y` of `Π` has no repeated dart only if no side
dart of `y` or `x` has `Π` across it (the field `side_cell` of `PocketWalk.CopyClean`,
`Estimating/OsinPocketCopyWalk.lean`).  On an optimal diagram a side arc can come back to a
relator face after leaving it.  Doubling that edge inside the relator face
(`FaceEdgeDoubling.diagram`) puts a G-cell digon between the relator face and the side.
Every old dart, face set and label survives.

* `IsCellSideDart`: a dart of a relator face with at least two darts, lying in no region of
  the family, whose reverse is a left or right side dart of a region of the family.
* `cellSideCount`: the number of cell-side darts.
* `CellSideThickeningStatement`: a distinguished section family has one over the same cuts,
  on an O-equivalent diagram, with no cell-side dart.  Its regions correspond to the old
  ones, with the same weight, target profiles and source indices.  The output shape is that
  of `OuterSpurThickening.OuterSpurThickeningStatement`.

A relator face with one dart is left out, because `FaceEdgeDoubling` needs two darts.  At the
source cell of a nondegenerate exterior region, that one dart lies in the source arc.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellSideThickening

open HullSC Embedded
open scoped Classical

universe u w v

section Darts

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- A **cell-side dart** of a family of regions: a dart of a relator face with at least two
darts, lying in no region of the family, whose reverse is a left or right side dart of a region
of the family. -/
def IsCellSideDart (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) (x : Delta.toCombMap.Dart) : Prop :=
  (∃ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf x = C.face) ∧
    1 < (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts.length ∧
      (∀ a ∈ family, Delta.toCombMap.faceOf x ∉ a.1) ∧
        ∃ a ∈ family, Delta.toCombMap.alpha x ∈ a.2.rightSide ++ a.2.leftSide

/-- The number of cell-side darts. -/
noncomputable def cellSideCount (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) : ℕ :=
  (Finset.univ.filter (IsCellSideDart Delta family)).card

/-- No cell-side dart exactly when the count is zero. -/
theorem cellSideCount_eq_zero_iff (Delta : DiscDiagram.{u, w, v} W)
    (family : Finset (RegionCandidate D eps Delta)) :
    cellSideCount Delta family = 0 ↔ ∀ x, ¬ IsCellSideDart Delta family x := by
  unfold cellSideCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x
    exact h (Finset.mem_univ x)
  · intro h x _
    exact h x

end Darts

/-- **Cell-side thickening.**  A distinguished section family has a distinguished section
family over the same cuts whose diagram is O-equivalent to the old one and has no cell-side
dart.  Its regions correspond bijectively to the old ones, with the same total weight, and
every region keeps its target profile and the index of its source cell. -/
def CellSideThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsCellSideDart S'.diagram S'.family x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val

end GroupApproximation.GGT.VanKampen.CellSideThickening

#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.cellSideCount_eq_zero_iff
