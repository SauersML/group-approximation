import GroupApproximation.GGT.VanKampen.SurgeryGFaceMerge
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.GGT.VanKampen.FaceSetWordHomotopyCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Darts, face sets and carriers through a G-face merge

`GFaceMerge.diagram` retains every dart off the deleted edge, with its label, edge
reversal and (away from the two merged faces) its face rotation.  This file records that
dictionary, the first half of the transport of contiguity regions avoiding the two merged
faces (`SurgeryGFaceMergeRegions` is the second).

A dart is **off the edge** when it is neither `dart` nor `alpha dart`; every dart on a face
other than the two merged ones is off the edge (`offEdge_of_faceOf_off`).  On lists of such
darts `keep` forgets nothing (`map_keep_val`, `map_keep_injective`, `nodup_map_keep`).  The
dictionary:

* edge reversal, face rotation off the merged faces, and faces (`alpha_keep`,
  `facePerm_keep`, `faceOf_keep_mem_faceSet_iff`);
* face sets avoiding the merged faces, through `faceSet s = s.image kept`
  (`kept_mem_faceSet_iff`, `merged_not_mem_faceSet`, `faceSet_disjoint_iff`, `faceSet_inj`);
* kept traversals and words (`faceBoundary_kept_darts`, `faceWord_kept`);
* the carriers of contiguity regions (`cellDarts_eq`, `outerDarts_eq`, `targetDarts_eq`),
  their reversals and arcs (`invDarts_map`, `reverseDarts_mapTo`, `targetBoundaryDarts_map`),
  and their words (`dartWord_map`).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge

open scoped Classical
open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (R : GFaceMerge Delta)

/-! ## Darts off the deleted edge -/

theorem offEdge_of_faceOf_off {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ≠ R.first ∧ Delta.toCombMap.faceOf d ≠ R.second) :
    d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart :=
  let h := EdgeDeletion.avoid_of_off hd rfl
  ⟨h.1, h.2.1⟩

theorem offEdge_alpha {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    Delta.toCombMap.alpha d ≠ R.dart ∧
      Delta.toCombMap.alpha d ≠ Delta.toCombMap.alpha R.dart := by
  refine ⟨fun h => hd.2 ?_, fun h => hd.1 (Delta.toCombMap.alpha.injective h)⟩
  rw [← h, Delta.toCombMap.alpha_involutive]

theorem offEdge_of_faceOf_alpha_off {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ R.first ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ≠ R.second) :
    d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := by
  have h := R.offEdge_of_faceOf_off hd
  refine ⟨fun he => h.2 (congrArg Delta.toCombMap.alpha he), fun he => h.1 ?_⟩
  rw [he, Delta.toCombMap.alpha_involutive]

theorem off_of_mem {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    {g : Delta.toCombMap.Face} (hg : g ∈ s) : g ≠ R.first ∧ g ≠ R.second :=
  ⟨fun h => hs.1 (h ▸ hg), fun h => hs.2 (h ▸ hg)⟩

theorem map_keep_val {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    (l.map R.keep).map R.val = l := by
  induction l with
  | nil => rfl
  | cons d t ih =>
      exact congrArg₂ List.cons (R.val_keep (hl d List.mem_cons_self))
        (ih fun e he => hl e (List.mem_cons_of_mem d he))

theorem map_keep_injective {l l' : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (hl' : ∀ d ∈ l', d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (h : l.map R.keep = l'.map R.keep) : l = l' := by
  rw [← R.map_keep_val hl, ← R.map_keep_val hl', h]

theorem nodup_map_keep {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) (hnodup : l.Nodup) :
    (l.map R.keep).Nodup :=
  hnodup.map_on fun x hx y hy hxy => by
    rw [← R.val_keep (hl x hx), ← R.val_keep (hl y hy), hxy]

theorem alpha_keep {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    R.diagram.toCombMap.alpha (R.keep d) = R.keep (Delta.toCombMap.alpha d) := by
  apply R.val_injective
  rw [R.val_alpha, R.val_keep hd, R.val_keep (R.offEdge_alpha hd)]

theorem facePerm_keep {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ≠ R.first ∧ Delta.toCombMap.faceOf d ≠ R.second) :
    R.diagram.toCombMap.facePerm (R.keep d) = R.keep (Delta.toCombMap.facePerm d) := by
  have havoid := EdgeDeletion.avoid_of_off hd rfl
  apply R.val_injective
  rw [R.val_keep ⟨havoid.2.2.1, havoid.2.2.2⟩]
  have h : R.val (R.diagram.toCombMap.facePerm (R.keep d)) =
      EdgeDeletion.next Delta.toCombMap R.dart (R.val (R.keep d)) :=
    EdgeDeletion.value_facePerm_eq_next Delta.toCombMap R.dart (R.keep d)
  rw [R.val_keep ⟨havoid.1, havoid.2.1⟩,
    EdgeDeletion.next_of_ne_of_ne Delta.toCombMap R.dart havoid.2.2.1 havoid.2.2.2] at h
  exact h

/-! ## Face sets -/

/-- The faces of the merge carrying an old face set. -/
noncomputable def faceSet (s : Finset Delta.toCombMap.Face) :
    Finset R.diagram.toCombMap.Face :=
  s.image R.kept

theorem mem_faceSet {s : Finset Delta.toCombMap.Face} {F : R.diagram.toCombMap.Face} :
    F ∈ R.faceSet s ↔ ∃ g ∈ s, R.kept g = F :=
  Finset.mem_image

theorem kept_mem_faceSet {s : Finset Delta.toCombMap.Face} {g : Delta.toCombMap.Face}
    (hg : g ∈ s) : R.kept g ∈ R.faceSet s :=
  Finset.mem_image_of_mem R.kept hg

theorem kept_mem_faceSet_iff {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) {g : Delta.toCombMap.Face}
    (hg : g ≠ R.first ∧ g ≠ R.second) : R.kept g ∈ R.faceSet s ↔ g ∈ s := by
  constructor
  · intro h
    obtain ⟨g', hg', heq⟩ := R.mem_faceSet.mp h
    exact R.kept_inj (R.off_of_mem hs hg') hg heq ▸ hg'
  · exact R.kept_mem_faceSet

theorem merged_not_mem_faceSet {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) : R.merged ∉ R.faceSet s := by
  intro h
  obtain ⟨g, hg, heq⟩ := R.mem_faceSet.mp h
  exact R.kept_ne_merged (R.off_of_mem hs hg) heq

theorem faceSet_disjoint_iff {s t : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) (ht : R.first ∉ t ∧ R.second ∉ t) :
    Disjoint (R.faceSet s) (R.faceSet t) ↔ Disjoint s t := by
  constructor
  · intro h
    exact Finset.disjoint_left.mpr fun g hgs hgt =>
      Finset.disjoint_left.mp h (R.kept_mem_faceSet hgs) (R.kept_mem_faceSet hgt)
  · intro h
    refine Finset.disjoint_left.mpr fun F hF hF' => ?_
    obtain ⟨g, hg, rfl⟩ := R.mem_faceSet.mp hF
    obtain ⟨g', hg', heq⟩ := R.mem_faceSet.mp hF'
    exact Finset.disjoint_left.mp h hg (R.kept_inj (R.off_of_mem ht hg') (R.off_of_mem hs hg) heq ▸ hg')

theorem faceSet_inj {s t : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (ht : R.first ∉ t ∧ R.second ∉ t) (h : R.faceSet s = R.faceSet t) : s = t := by
  ext g
  constructor
  · intro hg
    have hmem : R.kept g ∈ R.faceSet t := h ▸ R.kept_mem_faceSet hg
    obtain ⟨g', hg', heq⟩ := R.mem_faceSet.mp hmem
    exact R.kept_inj (R.off_of_mem ht hg') (R.off_of_mem hs hg) heq ▸ hg'
  · intro hg
    have hmem : R.kept g ∈ R.faceSet s := h.symm ▸ R.kept_mem_faceSet hg
    obtain ⟨g', hg', heq⟩ := R.mem_faceSet.mp hmem
    exact R.kept_inj (R.off_of_mem hs hg') (R.off_of_mem ht hg) heq ▸ hg'

theorem faceOf_keep_mem_faceSet_iff {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    R.diagram.toCombMap.faceOf (R.keep d) ∈ R.faceSet s ↔ Delta.toCombMap.faceOf d ∈ s := by
  by_cases hoff : Delta.toCombMap.faceOf d ≠ R.first ∧ Delta.toCombMap.faceOf d ≠ R.second
  · rw [R.faceOf_keep hoff, R.kept_mem_faceSet_iff hs hoff]
  · have hmerge : Delta.toCombMap.faceOf d = R.first ∨ Delta.toCombMap.faceOf d = R.second := by
      by_contra hc
      exact hoff (not_or.mp hc)
    rw [R.faceOf_keep_merged hd hmerge]
    constructor
    · intro h
      exact absurd h (R.merged_not_mem_faceSet hs)
    · intro h
      rcases hmerge with h' | h'
      · exact absurd (h' ▸ h) hs.1
      · exact absurd (h' ▸ h) hs.2

/-! ## Kept traversals -/

theorem faceBoundary_kept_darts (g : Delta.toCombMap.Face) (hg : g ≠ R.first ∧ g ≠ R.second) :
    (R.diagram.faceBoundary (R.kept g)).darts = (Delta.faceBoundary g).darts.map R.keep := by
  apply List.map_injective_iff.mpr R.val_injective
  rw [R.map_keep_val fun d hd => R.offEdge_of_faceOf_off
    (by rw [((Delta.faceBoundary g).mem_iff d).mp hd]; exact hg)]
  exact R.faceBoundary_kept_map_val g hg

theorem faceWord_kept (g : Delta.toCombMap.Face) (hg : g ≠ R.first ∧ g ≠ R.second) :
    R.diagram.faceWord (R.kept g) = Delta.faceWord g := by
  change (R.diagram.faceBoundary (R.kept g)).darts.map R.diagram.label =
    (Delta.faceBoundary g).darts.map Delta.label
  rw [R.faceBoundary_kept_darts g hg, List.map_map]
  exact List.map_congr_left fun d hd => congrArg Delta.label (R.val_keep
    (R.offEdge_of_faceOf_off (by rw [((Delta.faceBoundary g).mem_iff d).mp hd]; exact hg)))

theorem cell_face_eq (i : Fin Delta.rCellCount) :
    (Embedded.cell R.diagram (R.cellMap.indexEquiv i)).face =
      R.kept (Embedded.cell Delta i).face :=
  (congrArg RelatorCell.face (R.cellMap.indexed_cell i)).trans (R.cellMap.face_eq _)

/-! ## Carriers -/

theorem cellDarts_offEdge (i : Fin Delta.rCellCount) {d : Delta.toCombMap.Dart}
    (hd : d ∈ cellDarts Delta i) : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart :=
  R.offEdge_of_faceOf_off (by
    rw [((Delta.faceBoundary _).mem_iff d).mp hd]
    exact R.cells_avoid _ (Embedded.cell_mem Delta i))

theorem outerDarts_offEdge {d : Delta.toCombMap.Dart} (hd : d ∈ outerDarts Delta) :
    d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  apply R.offEdge_of_faceOf_alpha_off
  rw [Delta.toCombMap.alpha_involutive e,
    ((Delta.faceBoundary _).mem_iff e).mp (List.mem_reverse.mp he)]
  exact R.outer_off

theorem targetDarts_offEdge (target : Option (Fin Delta.rCellCount))
    {d : Delta.toCombMap.Dart} (hd : d ∈ targetDarts Delta target) :
    d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := by
  cases target with
  | none => exact R.outerDarts_offEdge hd
  | some i => exact R.cellDarts_offEdge i hd

theorem cellDarts_eq (i : Fin Delta.rCellCount) :
    cellDarts R.diagram (R.cellMap.indexEquiv i) = (cellDarts Delta i).map R.keep := by
  change (R.diagram.faceBoundary (Embedded.cell R.diagram (R.cellMap.indexEquiv i)).face).darts =
    (Delta.faceBoundary (Embedded.cell Delta i).face).darts.map R.keep
  rw [R.cell_face_eq i]
  exact R.faceBoundary_kept_darts _ (R.cells_avoid _ (Embedded.cell_mem Delta i))

theorem outerDarts_eq : outerDarts R.diagram = (outerDarts Delta).map R.keep := by
  apply List.map_injective_iff.mpr R.val_injective
  rw [R.map_keep_val fun d hd => R.outerDarts_offEdge hd]
  change ((R.diagram.faceBoundary R.diagram.outerFace).darts.reverse.map
      R.diagram.toCombMap.alpha).map R.val =
    (Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha
  calc ((R.diagram.faceBoundary R.diagram.outerFace).darts.reverse.map
        R.diagram.toCombMap.alpha).map R.val
      = ((R.diagram.faceBoundary R.diagram.outerFace).darts.reverse.map R.val).map
          Delta.toCombMap.alpha := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun x _ => R.val_alpha x
    _ = (((R.diagram.faceBoundary R.diagram.outerFace).darts.map R.val).reverse).map
          Delta.toCombMap.alpha := by
        rw [List.map_reverse]
    _ = (Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha := by
        rw [R.outerFace_eq, R.faceBoundary_kept_map_val Delta.outerFace R.outer_off]

theorem targetDarts_eq (target : Option (Fin Delta.rCellCount)) :
    targetDarts R.diagram (target.map R.cellMap.indexEquiv) =
      (targetDarts Delta target).map R.keep := by
  cases target with
  | none => exact R.outerDarts_eq
  | some i => exact R.cellDarts_eq i

theorem invDarts_map {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    invDarts R.diagram (l.map R.keep) = (invDarts Delta l).map R.keep := by
  change ((l.map R.keep).reverse).map R.diagram.toCombMap.alpha =
    (l.reverse.map Delta.toCombMap.alpha).map R.keep
  rw [← List.map_reverse, List.map_map, List.map_map]
  exact List.map_congr_left fun d hd => R.alpha_keep (hl d (List.mem_reverse.mp hd))

theorem dartWord_map {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    dartWord R.diagram (l.map R.keep) = dartWord Delta l := by
  change (l.map R.keep).map R.diagram.label = l.map Delta.label
  rw [List.map_map]
  exact List.map_congr_left fun d hd => congrArg Delta.label (R.val_keep (hl d hd))

theorem reverseDarts_mapTo {cycle : List Delta.toCombMap.Dart}
    (hcycle : ∀ d ∈ cycle, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (arc : CyclicArc cycle) {target : List R.diagram.toCombMap.Dart}
    (h : target = cycle.map R.keep) :
    (arc.mapTo R.keep h).reverseDarts = arc.reverseDarts.map R.keep := by
  change invDarts R.diagram (arc.mapTo R.keep h).darts = (invDarts Delta arc.darts).map R.keep
  rw [CyclicArc.mapTo_darts,
    R.invDarts_map fun d hd => hcycle d (arc.mem_cycle_of_mem_darts hd)]

theorem targetBoundaryDarts_map (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target)) :
    targetBoundaryDarts R.diagram (target.map R.cellMap.indexEquiv)
        (arc.mapTo R.keep (R.targetDarts_eq target)) =
      (targetBoundaryDarts Delta target arc).map R.keep := by
  cases target with
  | none => exact arc.mapTo_darts R.keep _
  | some i => exact R.reverseDarts_mapTo (fun d hd => R.cellDarts_offEdge i hd) arc _

end GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.map_keep_val
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.alpha_keep
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.facePerm_keep
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.faceOf_keep_mem_faceSet_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.faceSet_inj
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.faceWord_kept
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.cellDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.outerDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.targetBoundaryDarts_map
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.dartWord_map
