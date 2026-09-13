import GroupApproximation.GGT.VanKampen.SurgeryCellSideThickening
import GroupApproximation.GGT.VanKampen.SurgeryOuterSideThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# Cell-side thickening keeps the outer edge conditions

The copy for the pocket walk (`PocketWalk.CopyClean`) is built in three stages.
* The outer thickening `OuterSideThickening.outerSideThickening` gives no outer spur, no outer
  cell dart and no outer side dart.
* The cell-side thickening `CellSideThickening.cellSideThickening` gives no cell-side dart.
* The relator self-edge thickening gives `cell_self`.

An inner doubling at a relator face changes neither the exterior traversal nor the side darts:
every old dart embeds, `alpha` commutes with the embedding, and the doubled dart lies in the new
digon.  So the cell-side thickening keeps the outer conditions and the relator values.

* `faceOf_eq_outer_iff`: the new exterior consists of the images of the old exterior darts.
* `relatorValues_of_step`, `noOuterSpur_of_step`, `noOuterCellDart_of_step`,
  `noOuterSideDart_of_step`: one doubling keeps each condition.
* `OuterClean`, `outerClean_of_step`: the four conditions as one invariant of a family.
* `CellSideThickeningPreservingStatement`, `cellSideThickeningPreserving`: the cell-side
  thickening, taking and returning the outer conditions.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellSideThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Doubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}
  (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- The new exterior consists of the images of the old exterior darts. -/
theorem faceOf_eq_outer_iff (x : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart) :
    (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf x =
        (FaceEdgeDoubling.diagram Delta f j hlen hf).outerFace ↔
      ∃ e, Delta.toCombMap.faceOf e = Delta.outerFace ∧
        EdgeInsertion.embed Delta.toCombMap e = x := by
  rw [← ((FaceEdgeDoubling.diagram Delta f j hlen hf).faceBoundary
      (FaceEdgeDoubling.diagram Delta f j hlen hf).outerFace).mem_iff x,
    (FaceEdgeDoubling.embedding Delta f j hlen hf).outer,
    (FaceEdgeDoubling.embedding Delta f j hlen hf).face_boundary Delta.outerFace hf.symm,
    List.mem_map]
  exact exists_congr fun e => and_congr ((Delta.faceBoundary Delta.outerFace).mem_iff e) Iff.rfl

/-- The relator cells keep their words. -/
theorem relatorValues_of_step
    (hvalue : ∀ C ∈ Delta.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∀ C ∈ (FaceEdgeDoubling.diagram Delta f j hlen hf).relatorCells,
      RelLetter.listVal C.word ≠ 1 := by
  intro C' hC'
  have hC'' : C' ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC'
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC''
  exact hvalue C hC

/-- **The doubling creates no outer spur.** -/
theorem noOuterSpur_of_step (hfree : ∀ x, ¬ OuterSpurThickening.IsOuterSpur Delta x) :
    ∀ x, ¬ OuterSpurThickening.IsOuterSpur (FaceEdgeDoubling.diagram Delta f j hlen hf) x := by
  rintro x ⟨hx, hax⟩
  obtain ⟨e, he, rfl⟩ := (faceOf_eq_outer_iff Delta f j hlen hf x).mp hx
  have hax' : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
      (EdgeInsertion.embed Delta.toCombMap (Delta.toCombMap.alpha e)) =
        (FaceEdgeDoubling.diagram Delta f j hlen hf).outerFace := hax
  obtain ⟨e', he', hee'⟩ := (faceOf_eq_outer_iff Delta f j hlen hf _).mp hax'
  have hae : e' = Delta.toCombMap.alpha e := EdgeInsertion.embed_injective Delta.toCombMap hee'
  exact hfree e ⟨he, hae ▸ he'⟩

/-- **The doubling creates no outer cell dart.**  The face across an image exterior dart is the
image of the old face across it, or the digon when the old reverse is `w_j`. -/
theorem noOuterCellDart_of_step (hfree : ∀ x, ¬ OuterCellThickening.IsOuterCellDart Delta x) :
    ∀ x, ¬ OuterCellThickening.IsOuterCellDart (FaceEdgeDoubling.diagram Delta f j hlen hf) x := by
  rintro x ⟨hx, C', hC', hC'face⟩
  obtain ⟨e, he, rfl⟩ := (faceOf_eq_outer_iff Delta f j hlen hf x).mp hx
  have hC'' : C' ∈ Delta.relatorCells.map (FaceEdgeDoubling.cell Delta f j hlen hf) := hC'
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC''
  have hface : FaceEdgeDoubling.faceImage Delta f j hlen C.face =
      (FaceEdgeDoubling.map Delta f j hlen).faceOf
        (EdgeInsertion.embed Delta.toCombMap (Delta.toCombMap.alpha e)) := hC'face
  by_cases hae : Delta.toCombMap.alpha e = FaceEdgeDoubling.dart Delta f j
  · rw [hae, FaceEdgeDoubling.faceOf_embed_dart_digon] at hface
    exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C.face hface
  · rw [faceOf_embed_of_ne_dart Delta f j hlen hae] at hface
    exact hfree e ⟨he, C, hC, FaceEdgeDoubling.faceImage_injective Delta f j hlen hface⟩

/-- **The doubling creates no outer side dart.**  The side darts of a transported region are the
images of the old ones. -/
theorem noOuterSideDart_of_step (family : Finset (RegionCandidate D eps Delta))
    (havoid : FaceEdgeDoubling.FamilyArcAvoid Delta f j family)
    (hfree : ∀ x, ¬ OuterSideThickening.IsOuterSideDart Delta family x) :
    ∀ x, ¬ OuterSideThickening.IsOuterSideDart (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (FaceEdgeDoubling.regionFamilyOfArcs Delta f j hlen hf family havoid) x := by
  rintro x ⟨hx, a', ha', hside⟩
  obtain ⟨e, he, rfl⟩ := (faceOf_eq_outer_iff Delta f j hlen hf x).mp hx
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha'
  have hmap : EdgeInsertion.embed Delta.toCombMap (Delta.toCombMap.alpha e) ∈
      (b.val.2.rightSide ++ b.val.2.leftSide).map
        (FaceEdgeDoubling.embedding Delta f j hlen hf).darts := by
    rw [List.map_append]
    exact hside
  obtain ⟨d, hd, hde⟩ := List.mem_map.mp hmap
  have hda : d = Delta.toCombMap.alpha e := EdgeInsertion.embed_injective Delta.toCombMap hde
  exact hfree e ⟨he, b.val, b.property, hda ▸ hd⟩

end Doubling

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- The relator values and the three outer conditions, as one invariant of a family. -/
def OuterClean (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
    (∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) ∧
      (∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) ∧
        ∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x

/-- One doubling step keeps the invariant. -/
theorem outerClean_of_step (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family) (hS : OuterClean S) :
    OuterClean (sectionFamilyOfArcs S f j hlen hf havoid) :=
  ⟨relatorValues_of_step S.diagram f j hlen hf hS.1,
    noOuterSpur_of_step S.diagram f j hlen hf hS.2.1,
    noOuterCellDart_of_step S.diagram f j hlen hf hS.2.2.1,
    noOuterSideDart_of_step S.diagram f j hlen hf S.family havoid hS.2.2.2⟩

end Family

/-- **Cell-side thickening keeping the outer conditions.**  The shape of
`OuterSideThickening.OuterSideThickeningStatement`: the hypotheses and conclusions of the outer
stage are taken and returned, and no cell-side dart is added to the conclusion. -/
def CellSideThickeningPreservingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    1 < Delta.boundaryWord.length →
      (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
        (∀ x, ¬ OuterSpurThickening.IsOuterSpur S.diagram x) →
          (∀ x, ¬ OuterCellThickening.IsOuterCellDart S.diagram x) →
            (∀ x, ¬ OuterSideThickening.IsOuterSideDart S.diagram S.family x) →
              ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
                (e : S.family ≃ S'.family),
                Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
                  1 < Delta.boundaryWord.length ∧
                  (∀ x, ¬ IsCellSideDart S'.diagram S'.family x) ∧
                  (∀ x, ¬ OuterSpurThickening.IsOuterSpur S'.diagram x) ∧
                  (∀ x, ¬ OuterCellThickening.IsOuterCellDart S'.diagram x) ∧
                  (∀ x, ¬ OuterSideThickening.IsOuterSideDart S'.diagram S'.family x) ∧
                  (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                  S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                  ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                    (e a).1.2.source.val = a.1.2.source.val

theorem cellSideThickeningPreserving : CellSideThickeningPreservingStatement.{u, w, v} := by
  unfold CellSideThickeningPreservingStatement
  intro _ _ _ _ _ _ _ _ _ _ S hlen0 hvalue hspur hcell hside
  obtain ⟨S', e, hequiv, hfree, hweight, hprofile, hvalue', hspur', hcell', hside'⟩ :=
    exists_cellSideFree_of_invariant OuterClean
      (fun S f j hlen hf havoid hS => outerClean_of_step S f j hlen hf havoid hS) S
      ⟨hvalue, hspur, hcell, hside⟩
  exact ⟨S', e, hequiv, hlen0, hfree, hspur', hcell', hside', hvalue', hweight, hprofile⟩

end GroupApproximation.GGT.VanKampen.CellSideThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.cellSideThickeningPreserving
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.faceOf_eq_outer_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.noOuterSpur_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.noOuterCellDart_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.noOuterSideDart_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.CellSideThickening.outerClean_of_step
