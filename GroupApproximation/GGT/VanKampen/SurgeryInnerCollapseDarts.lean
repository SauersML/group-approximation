import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapse
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Darts, faces and carriers through an inner G-region collapse

`InnerGRegion.diagram` retains every dart that is not internal to the collapsed region,
with its label, edge reversal and (away from the region) its face rotation.  This file
records that dart-level dictionary, as the first half of the transport of contiguity
regions avoiding the collapsed faces (the second half, face-set boundaries, shellings,
contiguity geometry and region families, builds on it).

`InnerGRegion.keep` is the total dart map: a retained dart to itself, an internal dart
to one fixed retained dart.  Every list that the transport moves consists of retained
darts, and on such lists `keep` is injective and forgets nothing
(`map_keep_val`, `map_keep_injective`, `nodup_map_keep`).  The dictionary:

* edge reversal, face rotation outside the region, and faces (`alpha_keep`,
  `facePerm_keep`, `faceOf_keep`, `faceOf_keep_of_mem`);
* face sets avoiding the region, through `faceSet` (`faceOf_keep_mem_faceSet_iff`);
* the carriers of contiguity regions: relator-cell cycles, the exterior cycle and target
  cycles (`cellDarts_eq`, `outerDarts_eq`, `targetDarts_eq`), their reversals and arcs
  (`invDarts_map`, `reverseDarts_mapTo`, `targetBoundaryDarts_map`), and their words
  (`dartWord_map`).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion

open HullSC MapCollapse Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (R : InnerGRegion Delta)

/-! ## Retained darts -/

theorem not_internal_of_faceOf_not_mem {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ∉ R.faces) :
    ¬ InternalDart Delta.toCombMap R.faces d :=
  fun h => hd h.1

theorem not_internal_of_faceOf_alpha_not_mem {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉ R.faces) :
    ¬ InternalDart Delta.toCombMap R.faces d :=
  fun h => hd h.2

theorem not_internal_alpha {d : Delta.toCombMap.Dart}
    (hd : ¬ InternalDart Delta.toCombMap R.faces d) :
    ¬ InternalDart Delta.toCombMap R.faces (Delta.toCombMap.alpha d) :=
  fun h => hd ((internalDart_alpha_iff Delta.toCombMap R.faces d).mp h)

/-- The base dart of the region's boundary cycle is retained. -/
theorem head_not_internal :
    ¬ InternalDart Delta.toCombMap R.faces
      (R.boundary.cycle.head R.boundary.cycle_nonempty) := by
  have hb := (R.boundary.cycle_mem_iff _).mp (List.head_mem R.boundary.cycle_nonempty)
  exact fun h => hb.2 h.2

open scoped Classical in
/-- **The dart map of the collapse**: a retained dart to itself, an internal dart to the
base dart of the region's boundary cycle. -/
noncomputable def keep (d : Delta.toCombMap.Dart) : R.diagram.toCombMap.Dart :=
  (if h : InternalDart Delta.toCombMap R.faces d then
    ⟨R.boundary.cycle.head R.boundary.cycle_nonempty, R.head_not_internal⟩
  else ⟨d, h⟩ : KeptDart Delta.toCombMap R.faces)

theorem keep_val {d : Delta.toCombMap.Dart}
    (hd : ¬ InternalDart Delta.toCombMap R.faces d) : (R.keep d).1 = d := by
  simp [keep, hd]

theorem map_keep_val {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d) :
    (l.map R.keep).map Subtype.val = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [List.map_cons, List.map_cons, R.keep_val (hl d List.mem_cons_self),
      ih fun e he => hl e (List.mem_cons_of_mem _ he)]

theorem map_keep_injective {l l' : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d)
    (hl' : ∀ d ∈ l', ¬ InternalDart Delta.toCombMap R.faces d)
    (h : l.map R.keep = l'.map R.keep) : l = l' := by
  have h' := congrArg (List.map Subtype.val) h
  rwa [R.map_keep_val hl, R.map_keep_val hl'] at h'

theorem nodup_map_keep {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d) (hnodup : l.Nodup) :
    (l.map R.keep).Nodup :=
  List.Nodup.map_on (fun x hx y hy hxy =>
    (R.keep_val (hl x hx)).symm.trans ((congrArg Subtype.val hxy).trans
      (R.keep_val (hl y hy)))) hnodup

/-! ## Edge reversal, face rotation, faces -/

theorem alpha_keep {d : Delta.toCombMap.Dart}
    (hd : ¬ InternalDart Delta.toCombMap R.faces d) :
    R.diagram.toCombMap.alpha (R.keep d) = R.keep (Delta.toCombMap.alpha d) := by
  apply Subtype.ext
  change Delta.toCombMap.alpha (R.keep d).1 = (R.keep (Delta.toCombMap.alpha d)).1
  rw [R.keep_val hd, R.keep_val (R.not_internal_alpha hd)]

theorem facePerm_keep {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ∉ R.faces) :
    R.diagram.toCombMap.facePerm (R.keep d) = R.keep (Delta.toCombMap.facePerm d) := by
  have hnot := R.not_internal_of_faceOf_not_mem hd
  have hperm : Delta.toCombMap.faceOf (Delta.toCombMap.facePerm d) ∉ R.faces := by
    rw [Delta.toCombMap.faceOf_facePerm]
    exact hd
  apply Subtype.ext
  refine (replaceGRegion_facePerm_val_of_notMem Delta.toCombMap R.faces R.region
    (R.keep d) ?_).trans ?_
  · rw [R.keep_val hnot]
    exact hd
  · rw [R.keep_val hnot, R.keep_val (R.not_internal_of_faceOf_not_mem hperm)]

theorem faceOf_keep {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ∉ R.faces) :
    R.diagram.toCombMap.faceOf (R.keep d) =
      keptFace Delta.toCombMap R.faces R.region (Delta.toCombMap.faceOf d) hd := by
  have hnot := R.not_internal_of_faceOf_not_mem hd
  refine (faceOf_eq_keptFace Delta.toCombMap R.faces R.region (R.keep d) ?_).trans ?_
  · rw [R.keep_val hnot]
    exact hd
  · exact keptFace_congr Delta.toCombMap R.faces R.region _ _ _ _ (by rw [R.keep_val hnot])

theorem faceOf_keep_of_mem {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ∈ R.faces)
    (hnot : ¬ InternalDart Delta.toCombMap R.faces d) :
    R.diagram.toCombMap.faceOf (R.keep d) = newFace Delta.toCombMap R.faces R.region := by
  refine faceOf_eq_newFace Delta.toCombMap R.faces R.region (R.keep d) ?_
  rw [R.keep_val hnot]
  exact hd

/-! ## Face sets avoiding the region -/

open scoped Classical in
/-- The image of a face set under the face map of the collapse. -/
noncomputable def faceSet (s : Finset Delta.toCombMap.Face) :
    Finset R.diagram.toCombMap.Face :=
  s.image R.faceMap

open scoped Classical in
theorem keptFace_mem_faceSet_iff {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    {g : Delta.toCombMap.Face} (hg : g ∉ R.faces) :
    keptFace Delta.toCombMap R.faces R.region g hg ∈ R.faceSet s ↔ g ∈ s := by
  unfold faceSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g', hg's, hmap⟩
    have hg'R : g' ∉ R.faces := Finset.disjoint_left.mp hs hg's
    rw [R.faceMap_of_not_mem hg'R] at hmap
    rw [← keptFace_inj Delta.toCombMap R.faces R.region _ _ hg'R hg hmap]
    exact hg's
  · intro hgs
    exact ⟨g, hgs, R.faceMap_of_not_mem hg⟩

open scoped Classical in
theorem newFace_not_mem_faceSet {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces) :
    newFace Delta.toCombMap R.faces R.region ∉ R.faceSet s := by
  unfold faceSet
  rw [Finset.mem_image]
  rintro ⟨g, hgs, hmap⟩
  rw [R.faceMap_of_not_mem (Finset.disjoint_left.mp hs hgs)] at hmap
  exact keptFace_ne_newFace Delta.toCombMap R.faces R.region _ _ hmap

theorem faceOf_keep_mem_faceSet_iff {s : Finset Delta.toCombMap.Face}
    (hs : Disjoint s R.faces) {d : Delta.toCombMap.Dart}
    (hd : ¬ InternalDart Delta.toCombMap R.faces d) :
    R.diagram.toCombMap.faceOf (R.keep d) ∈ R.faceSet s ↔ Delta.toCombMap.faceOf d ∈ s := by
  by_cases hmem : Delta.toCombMap.faceOf d ∈ R.faces
  · rw [R.faceOf_keep_of_mem hmem hd]
    exact ⟨fun h => (R.newFace_not_mem_faceSet hs h).elim,
      fun h => (Finset.disjoint_left.mp hs h hmem).elim⟩
  · rw [R.faceOf_keep hmem, R.keptFace_mem_faceSet_iff hs hmem]

/-! ## Carriers -/

theorem cellDarts_not_internal (i : Fin Delta.rCellCount) {d : Delta.toCombMap.Dart}
    (hd : d ∈ cellDarts Delta i) : ¬ InternalDart Delta.toCombMap R.faces d := by
  apply R.not_internal_of_faceOf_not_mem
  rw [((Delta.faceBoundary _).mem_iff d).mp hd]
  exact R.cells_avoid _ (cell_mem Delta i)

theorem outerDarts_not_internal {d : Delta.toCombMap.Dart} (hd : d ∈ outerDarts Delta) :
    ¬ InternalDart Delta.toCombMap R.faces d := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  apply R.not_internal_of_faceOf_alpha_not_mem
  rw [Delta.toCombMap.alpha_involutive e,
    ((Delta.faceBoundary _).mem_iff e).mp (List.mem_reverse.mp he)]
  exact R.outer_not_mem

theorem targetDarts_not_internal (target : Option (Fin Delta.rCellCount))
    {d : Delta.toCombMap.Dart} (hd : d ∈ targetDarts Delta target) :
    ¬ InternalDart Delta.toCombMap R.faces d := by
  cases target with
  | none => exact R.outerDarts_not_internal hd
  | some i => exact R.cellDarts_not_internal i hd

theorem cellDarts_eq (i : Fin Delta.rCellCount) :
    cellDarts R.diagram (R.cellMap.indexEquiv i) = (cellDarts Delta i).map R.keep := by
  have hface : (cell Delta i).face ∉ R.faces := R.cells_avoid _ (cell_mem Delta i)
  apply List.map_injective_iff.mpr Subtype.val_injective
  rw [R.map_keep_val fun d hd => R.cellDarts_not_internal i hd]
  change ((R.diagram.faceBoundary (cell R.diagram (R.cellMap.indexEquiv i)).face).darts).map
    Subtype.val = (Delta.faceBoundary (cell Delta i).face).darts
  rw [R.cellMap.indexed_cell, R.cellMap.face_eq, R.faceMap_of_not_mem hface]
  exact replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap R.faces R.region
    Delta.faceBoundary _ hface

theorem outerDarts_eq : outerDarts R.diagram = (outerDarts Delta).map R.keep := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  rw [R.map_keep_val fun d hd => R.outerDarts_not_internal hd]
  have hmap : (R.diagram.faceBoundary R.diagram.outerFace).darts.map Subtype.val =
      (Delta.faceBoundary Delta.outerFace).darts :=
    replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap R.faces R.region
      Delta.faceBoundary Delta.outerFace R.outer_not_mem
  change ((R.diagram.faceBoundary R.diagram.outerFace).darts.reverse.map
      R.diagram.toCombMap.alpha).map Subtype.val =
    (Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha
  calc ((R.diagram.faceBoundary R.diagram.outerFace).darts.reverse.map
        R.diagram.toCombMap.alpha).map Subtype.val
      = ((R.diagram.faceBoundary R.diagram.outerFace).darts.reverse.map Subtype.val).map
          Delta.toCombMap.alpha := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun _ _ => rfl
    _ = (((R.diagram.faceBoundary R.diagram.outerFace).darts.map Subtype.val).reverse).map
          Delta.toCombMap.alpha := by
        rw [List.map_reverse]
    _ = (Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha := by
        rw [hmap]

theorem targetDarts_eq (target : Option (Fin Delta.rCellCount)) :
    targetDarts R.diagram (target.map R.cellMap.indexEquiv) =
      (targetDarts Delta target).map R.keep := by
  cases target with
  | none => exact R.outerDarts_eq
  | some i => exact R.cellDarts_eq i

theorem invDarts_map {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d) :
    invDarts R.diagram (l.map R.keep) = (invDarts Delta l).map R.keep := by
  change ((l.map R.keep).reverse).map R.diagram.toCombMap.alpha =
    (l.reverse.map Delta.toCombMap.alpha).map R.keep
  rw [← List.map_reverse, List.map_map, List.map_map]
  exact List.map_congr_left fun d hd => R.alpha_keep (hl d (List.mem_reverse.mp hd))

theorem dartWord_map {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d) :
    dartWord R.diagram (l.map R.keep) = dartWord Delta l := by
  change (l.map R.keep).map (fun d => Delta.label d.1) = l.map Delta.label
  rw [List.map_map]
  exact List.map_congr_left fun d hd => congrArg Delta.label (R.keep_val (hl d hd))

theorem reverseDarts_mapTo {cycle : List Delta.toCombMap.Dart}
    (hcycle : ∀ d ∈ cycle, ¬ InternalDart Delta.toCombMap R.faces d)
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
  | some i => exact R.reverseDarts_mapTo (fun d hd => R.cellDarts_not_internal i hd) arc _

end GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.map_keep_val
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.facePerm_keep
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.faceOf_keep_mem_faceSet_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.cellDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.outerDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.targetBoundaryDarts_map
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.dartWord_map
