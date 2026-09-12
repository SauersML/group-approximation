import GroupApproximation.GGT.VanKampen.VanKampenCancel
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.Meta.AxiomGuard

/-!
# Face cycles of a collapsed G-region

`Surgery.InnerGRegion.diagram` collapses a G-region of a disc diagram into one G-face.
This file reads face cycles of the collapse off face cycles of the original diagram,
and identifies the relator faces of the collapse.  It is the vocabulary of the O52
surgery (`Estimating/OsinAppendixO52Surgery.lean`).

* `Surgery.InnerGRegion.exists_keptFaceCycle`, `.exists_newFaceCycle`: lifts of face
  cycles.
* `Surgery.InnerGRegion.faceOf_kept`, `.faceOf_new`, `.keptFace_mem_relatorFaces`,
  `.newFace_not_mem_relatorFaces`: faces and relator faces of the collapse.
* `Embedded.cell_face_ne`: distinct cells lie on distinct faces.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC RelatorDefectBudget

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- Distinct relator cells lie on distinct faces. -/
theorem Embedded.cell_face_ne {Delta : DiscDiagram.{u, w, v} W}
    {i j : Fin Delta.rCellCount} (hij : i ≠ j) :
    (Embedded.cell Delta i).face ≠ (Embedded.cell Delta j).face := by
  intro h
  apply hij
  have hC : Embedded.cell Delta i = Embedded.cell Delta j :=
    List.inj_on_of_nodup_map Delta.relatorCell_faces_nodup (Embedded.cell_mem Delta i)
      (Embedded.cell_mem Delta j) h
  exact (List.Nodup.of_map RelatorCell.face Delta.relatorCell_faces_nodup).get_inj_iff.mp hC

namespace Surgery.InnerGRegion

variable {Delta : DiscDiagram.{u, w, v} W} (R : Surgery.InnerGRegion Delta)

/-- **A face cycle of a kept face**, lifted from the original map. -/
theorem exists_keptFaceCycle {g : Delta.toCombMap.Face} (hg : g ∉ R.faces)
    {d : Delta.toCombMap.Dart} {rest : List Delta.toCombMap.Dart}
    (hcyc : Delta.toCombMap.IsFaceCycle (d :: rest)) (hd : Delta.toCombMap.faceOf d = g) :
    ∃ (d' : R.diagram.toCombMap.Dart) (rest' : List R.diagram.toCombMap.Dart),
      d'.1 = d ∧ R.diagram.toCombMap.IsFaceCycle (d' :: rest') ∧
        rest'.map (fun x : R.diagram.toCombMap.Dart => x.1) = rest := by
  have hmap : (R.diagram.faceBoundary
      (Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region g hg)).darts.map
        Subtype.val = (Delta.faceBoundary g).darts :=
    Surgery.MapCollapse.replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap R.faces
      R.region Delta.faceBoundary g hg
  have hdmem : d ∈ (R.diagram.faceBoundary
      (Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region g hg)).darts.map
        Subtype.val :=
    (congrArg (fun L => d ∈ L) hmap).mpr (((Delta.faceBoundary g).mem_iff d).mpr hd)
  obtain ⟨d', hd'mem, hd'val⟩ := List.mem_map.mp hdmem
  obtain ⟨k, rest', _, hrot⟩ := (R.diagram.faceBoundary
    (Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region g hg)).isFaceCycle.exists_rotate_cons
      hd'mem
  have hcyc' : R.diagram.toCombMap.IsFaceCycle (d' :: rest') :=
    (congrArg R.diagram.toCombMap.IsFaceCycle hrot).mp ((R.diagram.faceBoundary
      (Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region g hg)).isFaceCycle.rotate k)
  have hmapRot : (d' :: rest').map Subtype.val = (Delta.faceBoundary g).darts.rotate k :=
    ((congrArg (List.map Subtype.val) hrot).symm.trans (List.map_rotate _ _ _)).trans
      (congrArg (fun L => L.rotate k) hmap)
  have hΔ : Delta.toCombMap.IsFaceCycle ((d' :: rest').map Subtype.val) :=
    (congrArg Delta.toCombMap.IsFaceCycle hmapRot).mpr
      ((Delta.faceBoundary g).isFaceCycle.rotate k)
  have heq := hΔ.eq_of_head_eq hcyc hd'val
  exact ⟨d', rest', hd'val, hcyc', (List.cons.inj heq).2⟩

/-- **A face cycle of the collapsed face**, read off the boundary cycle of the region. -/
theorem exists_newFaceCycle {d : Delta.toCombMap.Dart} {rest : List Delta.toCombMap.Dart}
    (hcycle : R.boundary.cycle = d :: rest) :
    ∃ (d' : R.diagram.toCombMap.Dart) (rest' : List R.diagram.toCombMap.Dart),
      d'.1 = d ∧ R.diagram.toCombMap.IsFaceCycle (d' :: rest') ∧
        rest'.map (fun x : R.diagram.toCombMap.Dart => x.1) = rest := by
  have hmap : (R.diagram.faceBoundary
      (Surgery.MapCollapse.newFace Delta.toCombMap R.faces R.region)).darts.map
        Subtype.val = d :: rest :=
    (Surgery.MapCollapse.replaceGRegionFaceBoundary_newFace_map_val Delta.toCombMap R.faces
      R.region Delta.faceBoundary).trans hcycle
  obtain ⟨d', rest', hsplit, hd', hrest⟩ := List.map_eq_cons_iff.mp hmap
  exact ⟨d', rest', hd', (congrArg R.diagram.toCombMap.IsFaceCycle hsplit).mp
    (R.diagram.faceBoundary
      (Surgery.MapCollapse.newFace Delta.toCombMap R.faces R.region)).isFaceCycle, hrest⟩

/-- A retained dart based outside the region lies on the kept face of its old face. -/
theorem faceOf_kept (d : R.diagram.toCombMap.Dart) {g : Delta.toCombMap.Face}
    (hg : g ∉ R.faces) (hd : Delta.toCombMap.faceOf d.1 = g) :
    R.diagram.toCombMap.faceOf d =
      Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region g hg :=
  (Surgery.MapCollapse.faceOf_eq_keptFace Delta.toCombMap R.faces R.region d
    (fun h => hg ((congrArg (fun z => z ∈ R.faces) hd).mp h))).trans
    (Surgery.MapCollapse.keptFace_congr Delta.toCombMap R.faces R.region _ _ _ hg hd)

/-- A retained dart based inside the region lies on the new face. -/
theorem faceOf_new (d : R.diagram.toCombMap.Dart)
    (hd : Delta.toCombMap.faceOf d.1 ∈ R.faces) :
    R.diagram.toCombMap.faceOf d =
      Surgery.MapCollapse.newFace Delta.toCombMap R.faces R.region :=
  Surgery.MapCollapse.faceOf_eq_newFace Delta.toCombMap R.faces R.region d hd

/-- The kept face of a relator cell is a relator face of the collapse. -/
theorem keptFace_mem_relatorFaces (i : Fin Delta.rCellCount) :
    Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region
      (Embedded.cell Delta i).face (R.cells_avoid _ (Embedded.cell_mem Delta i)) ∈
        R.diagram.relatorFaces :=
  DiscDiagram.mem_relatorFaces.mpr ⟨R.cell (Embedded.cell Delta i),
    List.mem_map.mpr ⟨_, Embedded.cell_mem Delta i, rfl⟩,
    R.faceMap_of_not_mem (R.cells_avoid _ (Embedded.cell_mem Delta i))⟩

/-- The new face is not a relator face of the collapse. -/
theorem newFace_not_mem_relatorFaces :
    Surgery.MapCollapse.newFace Delta.toCombMap R.faces R.region ∉
      R.diagram.relatorFaces := by
  intro h
  obtain ⟨C', hC', hface⟩ := DiscDiagram.mem_relatorFaces.mp h
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
  exact Surgery.MapCollapse.keptFace_ne_newFace Delta.toCombMap R.faces R.region C.face
    (R.cells_avoid C hC) ((R.faceMap_of_not_mem (R.cells_avoid C hC)).symm.trans hface)

end Surgery.InnerGRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.cell_face_ne
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.exists_keptFaceCycle
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.exists_newFaceCycle
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.keptFace_mem_relatorFaces
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.newFace_not_mem_relatorFaces
