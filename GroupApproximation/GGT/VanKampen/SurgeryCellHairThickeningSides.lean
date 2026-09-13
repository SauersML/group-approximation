import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.GGT.VanKampen.SurgeryCellSideThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# Cell-side darts through the opening of a relator face

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The edge conditions
`PocketWalk.CopyClean` of the pocket walk are produced by a sequence of thickenings.  A cell-side
dart (`CellSideThickening.IsCellSideDart`) is a dart of a relator face whose reverse is a side
dart of a region; a diagram without them satisfies `CopyClean.side_cell`.  This file shows that
opening a relator face along one of its darts (`FaceEdgeDoubling.diagram`), as
`CellHairThickening` does for a cell hair, creates no cell-side dart.

A region carried through the doubling has as sides the images of its old sides under `embed`
(`exists_of_mem_sides`).  So the reverse of a new cell-side dart is `embed` of an old side dart,
and the dart itself is `embed` of that dart's reverse.  Its face is the image of an old relator
face with the same number of darts (`length_faceImage`), and no region contains a relator face
when no relator word has value one.  So an old cell-side dart already existed (`noCellSideDart`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellHairThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Sides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- The image of a face has as many darts as the face. -/
theorem length_faceImage (g : Delta.toCombMap.Face) :
    (FaceEdgeDoubling.boundary Delta f j hlen
        (FaceEdgeDoubling.faceImage Delta f j hlen g)).darts.length =
      (Delta.faceBoundary g).darts.length := by
  have h := congrArg List.length (FaceEdgeDoubling.boundary_faceImage_word Delta f j hlen g)
  simpa only [List.length_map] using h

/-- A side dart of a region carried through the doubling is the image of a side dart of the old
region. -/
theorem exists_of_mem_sides {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    {a : RegionCandidate D eps (FaceEdgeDoubling.diagram Delta f j hlen hf)}
    (ha : a ∈ FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid)
    {y : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart}
    (hy : y ∈ a.2.rightSide ++ a.2.leftSide) :
    ∃ b ∈ family, ∃ d ∈ b.2.rightSide ++ b.2.leftSide, embed Delta.toCombMap d = y := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  have hy' : y ∈ b.val.2.rightSide.map (FaceEdgeDoubling.embedding Delta f j hlen hf).darts ++
      b.val.2.leftSide.map (FaceEdgeDoubling.embedding Delta f j hlen hf).darts := hy
  rw [← List.map_append] at hy'
  obtain ⟨d, hd, hdy⟩ := List.mem_map.mp hy'
  exact ⟨b.val, b.property, d, hd, hdy⟩

/-- **Opening a relator face along a dart creates no cell-side dart**, when no relator word has
value one and the old family has no cell-side dart. -/
theorem noCellSideDart {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hfree : ∀ x, ¬ CellSideThickening.IsCellSideDart Delta family x) :
    ∀ x, ¬ CellSideThickening.IsCellSideDart (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid) x := by
  intro x hx
  obtain ⟨⟨C, hC, hCf⟩, hlenx, -, a, ha, hax⟩ := hx
  obtain ⟨b, hb, d, hd, hdx⟩ := exists_of_mem_sides Delta f j hlen hf family havoid ha hax
  have hxe : x = embed Delta.toCombMap (Delta.toCombMap.alpha d) := by
    have h := congrArg (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha hdx
    rw [(FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.alpha_involutive x] at h
    exact h.symm
  subst hxe
  have hC' : C ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC'
  have hface : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
      (embed Delta.toCombMap (Delta.toCombMap.alpha d)) =
        FaceEdgeDoubling.faceImage Delta f j hlen C₀.face := hCf
  by_cases had : Delta.toCombMap.alpha d = FaceEdgeDoubling.dart Delta f j
  · rw [had, faceOf_embed_dart Delta f j hlen hf] at hface
    exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C₀.face hface.symm
  · have hface2 := hface
    rw [faceOf_embed Delta f j hlen hf had] at hface2
    have hfd : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = C₀.face :=
      FaceEdgeDoubling.faceImage_injective Delta f j hlen hface2
    have h1 : ((FaceEdgeDoubling.diagram Delta f j hlen hf).faceBoundary
        ((FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
          (embed Delta.toCombMap (Delta.toCombMap.alpha d)))).darts.length =
        (Delta.faceBoundary (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length := by
      rw [faceOf_embed Delta f j hlen hf had]
      exact length_faceImage Delta f j hlen _
    refine hfree (Delta.toCombMap.alpha d)
      ⟨⟨C₀, hC₀, hfd⟩, lt_of_lt_of_eq hlenx h1, fun c _ => ?_, b, hb, ?_⟩
    · rw [hfd]
      exact relatorFace_not_mem hvalue hC₀ c
    · rw [Delta.toCombMap.alpha_involutive d]
      exact hd

end Sides

end GroupApproximation.GGT.VanKampen.CellHairThickening

#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.length_faceImage
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.exists_of_mem_sides
#audit_axioms GroupApproximation.GGT.VanKampen.CellHairThickening.noCellSideDart
