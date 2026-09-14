import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapse
import GroupApproximation.Meta.AxiomGuard

/-!
# Collapsing the faces behind a gap into the polygon face: model test

Osin (math/0411039v3, §9), proof of Lemma 9.4, Case 1, on class words
(`OsinLemma94ClassCaseGapSpanStatement`).  The proposed producer merges the polygon face with the faces
behind a gap into one G-face (`Surgery.InnerGRegion`), so that the class arc becomes one stretch of the
merged face walk and `GFaceWordInsertion.exists_quadrilateral_region_rotate` applies.  A hair gap is
first opened by `SurgeryCellHairThickening`, which puts a G-cell digon on the hair.

This module records where that route stops.

* `NoEdgeBetween Delta faces part`: no edge of `Delta` has a face of `part` on one side and a face of
  `faces` outside `part` on the other.
* `internalBoundaryMove_mem_part_iff`, `reflTransGen_internalBoundaryMove_mem_part_iff`,
  `boundaryStep_mem_part_iff`: a boundary step (`BoundaryStep`: once around the current face, then
  across internal edges) never changes the part.
* `FaceSetBoundary.false_of_noEdgeBetween`, `Surgery.InnerGRegion.false_of_noEdgeBetween`: a face set
  whose two parts share no edge has no single boundary cycle once both parts carry a boundary dart, so it
  is no `InnerGRegion`.

Consequence for the producer (hand application).  Let the relator cell `Π` read `p, h, α h, q` with a
hair `h`, and the polygon face read `α q, α p` across it at the base `x` of the hair.  The doubling of
`FaceEdgeDoubling` along `h` inserts a digon `{h, new}` inside `Π`, with vertices `x` and the tip.  Every
dart of the digon has `Π` across, and no dart of the polygon face has the digon across: the polygon face
and the digon meet only at `x`.  So `{polygon face, digon}` satisfies `NoEdgeBetween` with `part` the
polygon face, both parts carry boundary darts, and no collapse exists.  A bubble gap has the same shape:
the faces inside the gap loop lie on the other side of `Π` at `x` and share no edge with the polygon
face.  The merge of the polygon face with the faces behind a gap is therefore not available through
`Surgery.InnerGRegion` for any gap.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, "Hull's small cancellation theorem", through
Osin's Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}

/-- **Two parts of a face set with no edge between them.**  An edge with both faces in `faces` has both
in `part` or both outside `part`. -/
def NoEdgeBetween (Delta : DiscDiagram.{u, w, v} W)
    (faces part : Finset Delta.toCombMap.Face) : Prop :=
  ∀ d : Delta.toCombMap.Dart, Delta.toCombMap.faceOf d ∈ faces →
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ faces →
      (Delta.toCombMap.faceOf d ∈ part ↔
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ part)

/-- An internal move does not change the part. -/
theorem internalBoundaryMove_mem_part_iff {Delta : DiscDiagram.{u, w, v} W}
    {faces part : Finset Delta.toCombMap.Face} (hsplit : NoEdgeBetween Delta faces part)
    {d e : Delta.toCombMap.Dart} (h : InternalBoundaryMove Delta faces d e) :
    (Delta.toCombMap.faceOf d ∈ part ↔ Delta.toCombMap.faceOf e ∈ part) := by
  obtain ⟨hd, hda, rfl⟩ := h
  rw [Delta.toCombMap.faceOf_facePerm]
  exact hsplit d hd hda

/-- A run of internal moves does not change the part. -/
theorem reflTransGen_internalBoundaryMove_mem_part_iff {Delta : DiscDiagram.{u, w, v} W}
    {faces part : Finset Delta.toCombMap.Face} (hsplit : NoEdgeBetween Delta faces part)
    {d e : Delta.toCombMap.Dart}
    (h : Relation.ReflTransGen (InternalBoundaryMove Delta faces) d e) :
    (Delta.toCombMap.faceOf d ∈ part ↔ Delta.toCombMap.faceOf e ∈ part) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (internalBoundaryMove_mem_part_iff hsplit hstep)

/-- **A boundary step does not change the part**: it advances around the current face and crosses
internal edges only. -/
theorem boundaryStep_mem_part_iff {Delta : DiscDiagram.{u, w, v} W}
    {faces part : Finset Delta.toCombMap.Face} (hsplit : NoEdgeBetween Delta faces part)
    {d e : Delta.toCombMap.Dart} (h : BoundaryStep Delta faces d e) :
    (Delta.toCombMap.faceOf d ∈ part ↔ Delta.toCombMap.faceOf e ∈ part) := by
  rw [← Delta.toCombMap.faceOf_facePerm d]
  exact reflTransGen_internalBoundaryMove_mem_part_iff hsplit h.2.2

/-- **No single boundary cycle across a split.**  If the two parts of a face set share no edge and each
carries a boundary dart, the face set has no `FaceSetBoundary`. -/
theorem FaceSetBoundary.false_of_noEdgeBetween {Delta : DiscDiagram.{u, w, v} W}
    {faces part : Finset Delta.toCombMap.Face} (B : FaceSetBoundary Delta faces)
    (hsplit : NoEdgeBetween Delta faces part) {d₁ d₂ : Delta.toCombMap.Dart}
    (hd₁ : IsBoundaryDart Delta faces d₁) (hd₂ : IsBoundaryDart Delta faces d₂)
    (hin : Delta.toCombMap.faceOf d₁ ∈ part) (hout : Delta.toCombMap.faceOf d₂ ∉ part) :
    False := by
  have hall : ∀ i ∈ B.cycle,
      (Delta.toCombMap.faceOf i ∈ part ↔
        Delta.toCombMap.faceOf (B.cycle.head B.cycle_nonempty) ∈ part) := by
    refine List.IsChain.induction
      (fun i => Delta.toCombMap.faceOf i ∈ part ↔
        Delta.toCombMap.faceOf (B.cycle.head B.cycle_nonempty) ∈ part)
      B.cycle B.cycle_chain ?_ ?_
    · intro x y hxy hx
      exact (boundaryStep_mem_part_iff hsplit hxy).symm.trans hx
    · intro _
      exact Iff.rfl
  have h₁ := hall d₁ ((B.cycle_mem_iff d₁).2 hd₁)
  have h₂ := hall d₂ ((B.cycle_mem_iff d₂).2 hd₂)
  exact hout (h₂.2 (h₁.1 hin))

end Embedded

/-- **No collapse across a split**: a G-cell region whose two parts share no edge, each with a boundary
dart, is no `InnerGRegion`. -/
theorem Surgery.InnerGRegion.false_of_noEdgeBetween {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    (R : Surgery.InnerGRegion Delta) {part : Finset Delta.toCombMap.Face}
    (hsplit : Embedded.NoEdgeBetween Delta R.faces part) {d₁ d₂ : Delta.toCombMap.Dart}
    (hd₁ : Embedded.IsBoundaryDart Delta R.faces d₁)
    (hd₂ : Embedded.IsBoundaryDart Delta R.faces d₂)
    (hin : Delta.toCombMap.faceOf d₁ ∈ part) (hout : Delta.toCombMap.faceOf d₂ ∉ part) :
    False :=
  R.boundary.false_of_noEdgeBetween hsplit hd₁ hd₂ hin hout

end VanKampen
end GGT
end GroupApproximation

open GroupApproximation.GGT.VanKampen

#audit_axioms Embedded.boundaryStep_mem_part_iff
#audit_axioms Embedded.FaceSetBoundary.false_of_noEdgeBetween
#audit_axioms Surgery.InnerGRegion.false_of_noEdgeBetween
