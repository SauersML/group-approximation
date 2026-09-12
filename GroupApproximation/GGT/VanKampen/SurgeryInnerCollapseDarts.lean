import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapse
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Darts, faces and carriers through an inner G-region collapse

`InnerGRegion.diagram` retains every dart that is not internal to the collapsed region,
with its label, edge reversal and (away from the region) its face rotation.  This file
records that dart-level dictionary, the first half of the transport of contiguity
regions avoiding the collapsed faces (`SurgeryInnerCollapseRegions` is the second).

The darts and faces of the collapse are, by definition, retained old darts and old or
merged faces, but only through the definitions `InnerGRegion.diagram`,
`MapCollapse.replaceGRegion` and `MapCollapse.reclosedMap`, which are not reducible.  So
this file first names the dictionary in terms of `R.diagram` itself: `R.val` (the old
dart under a dart of the collapse), `R.kept g hg` and `R.merged` (the kept and the new
face), `R.face` (the face map); every statement below uses only these, so every goal is
type-correct at the transparency `rw` checks.

`InnerGRegion.keep` is the total dart map: a retained dart to itself, an internal dart
to one fixed retained dart.  On lists of retained darts it forgets nothing
(`map_keep_val`, `map_keep_injective`, `nodup_map_keep`).  The dictionary:

* edge reversal, face rotation outside the region, and faces (`alpha_keep`,
  `facePerm_keep`, `faceOf_keep`, `faceOf_keep_of_mem`);
* face sets avoiding the region, through `faceSet` (`faceOf_keep_mem_faceSet_iff`);
* the carriers of contiguity regions (`cellDarts_eq`, `outerDarts_eq`, `targetDarts_eq`),
  their reversals and arcs (`invDarts_map`, `reverseDarts_mapTo`,
  `targetBoundaryDarts_map`), and their words (`dartWord_map`).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion

open MapCollapse
open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (R : InnerGRegion Delta)

/-! ## The dictionary, in terms of `R.diagram` -/

/-- The old dart underlying a dart of the collapse. -/
def val (x : R.diagram.toCombMap.Dart) : Delta.toCombMap.Dart :=
  (x : KeptDart Delta.toCombMap R.faces).1

theorem val_not_internal (x : R.diagram.toCombMap.Dart) :
    ¬ InternalDart Delta.toCombMap R.faces (R.val x) :=
  (x : KeptDart Delta.toCombMap R.faces).2

theorem val_injective : Function.Injective R.val :=
  fun _ _ h => Subtype.ext h

theorem val_alpha (x : R.diagram.toCombMap.Dart) :
    R.val (R.diagram.toCombMap.alpha x) = Delta.toCombMap.alpha (R.val x) :=
  rfl

theorem val_facePerm (x : R.diagram.toCombMap.Dart)
    (hx : Delta.toCombMap.faceOf (R.val x) ∉ R.faces) :
    R.val (R.diagram.toCombMap.facePerm x) = Delta.toCombMap.facePerm (R.val x) :=
  replaceGRegion_facePerm_val_of_notMem Delta.toCombMap R.faces R.region x hx

/-- The kept copy of an old face. -/
noncomputable def kept (g : Delta.toCombMap.Face) (hg : g ∉ R.faces) :
    R.diagram.toCombMap.Face :=
  keptFace Delta.toCombMap R.faces R.region g hg

/-- The new face bounded by the region's boundary cycle. -/
noncomputable def merged : R.diagram.toCombMap.Face :=
  newFace Delta.toCombMap R.faces R.region

/-- The face map of the collapse. -/
noncomputable def face (g : Delta.toCombMap.Face) : R.diagram.toCombMap.Face :=
  R.faceMap g

theorem kept_inj {g g' : Delta.toCombMap.Face} {hg : g ∉ R.faces} {hg' : g' ∉ R.faces}
    (h : R.kept g hg = R.kept g' hg') : g = g' :=
  keptFace_inj Delta.toCombMap R.faces R.region g g' hg hg' h

theorem kept_congr {g g' : Delta.toCombMap.Face} (hg : g ∉ R.faces) (hg' : g' ∉ R.faces)
    (h : g = g') : R.kept g hg = R.kept g' hg' :=
  keptFace_congr Delta.toCombMap R.faces R.region g g' hg hg' h

theorem kept_ne_merged (g : Delta.toCombMap.Face) (hg : g ∉ R.faces) :
    R.kept g hg ≠ R.merged :=
  keptFace_ne_newFace Delta.toCombMap R.faces R.region g hg

theorem face_of_not_mem {g : Delta.toCombMap.Face} (hg : g ∉ R.faces) :
    R.face g = R.kept g hg :=
  R.faceMap_of_not_mem hg

theorem face_of_mem {g : Delta.toCombMap.Face} (hg : g ∈ R.faces) : R.face g = R.merged :=
  R.faceMap_of_mem hg

theorem outerFace_eq : R.diagram.outerFace = R.kept Delta.outerFace R.outer_not_mem :=
  rfl

theorem faceOf_val_not_mem (x : R.diagram.toCombMap.Dart)
    (hx : Delta.toCombMap.faceOf (R.val x) ∉ R.faces) :
    R.diagram.toCombMap.faceOf x = R.kept (Delta.toCombMap.faceOf (R.val x)) hx :=
  faceOf_eq_keptFace Delta.toCombMap R.faces R.region x hx

theorem faceOf_val_mem (x : R.diagram.toCombMap.Dart)
    (hx : Delta.toCombMap.faceOf (R.val x) ∈ R.faces) :
    R.diagram.toCombMap.faceOf x = R.merged :=
  faceOf_eq_newFace Delta.toCombMap R.faces R.region x hx

theorem faceBoundary_kept_map_val (g : Delta.toCombMap.Face) (hg : g ∉ R.faces) :
    (R.diagram.faceBoundary (R.kept g hg)).darts.map R.val = (Delta.faceBoundary g).darts :=
  replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap R.faces R.region
    Delta.faceBoundary g hg

theorem faceBoundary_merged_map_val :
    (R.diagram.faceBoundary R.merged).darts.map R.val = R.boundary.cycle :=
  replaceGRegionFaceBoundary_newFace_map_val Delta.toCombMap R.faces R.region
    Delta.faceBoundary

theorem cell_face_eq (i : Fin Delta.rCellCount) :
    (Embedded.cell R.diagram (R.cellMap.indexEquiv i)).face =
      R.kept (Embedded.cell Delta i).face (R.cells_avoid _ (Embedded.cell_mem Delta i)) :=
  (congrArg RelatorCell.face (R.cellMap.indexed_cell i)).trans
    ((R.cellMap.face_eq _).trans (R.faceMap_of_not_mem _))

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

theorem val_keep {d : Delta.toCombMap.Dart}
    (hd : ¬ InternalDart Delta.toCombMap R.faces d) : R.val (R.keep d) = d := by
  simp [val, keep, hd]

theorem keep_val (x : R.diagram.toCombMap.Dart) : R.keep (R.val x) = x :=
  R.val_injective (R.val_keep (R.val_not_internal x))

theorem map_keep_val {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d) :
    (l.map R.keep).map R.val = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [List.map_cons, List.map_cons, R.val_keep (hl d List.mem_cons_self),
      ih fun e he => hl e (List.mem_cons_of_mem _ he)]

theorem map_keep_injective {l l' : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d)
    (hl' : ∀ d ∈ l', ¬ InternalDart Delta.toCombMap R.faces d)
    (h : l.map R.keep = l'.map R.keep) : l = l' := by
  have h' := congrArg (List.map R.val) h
  rwa [R.map_keep_val hl, R.map_keep_val hl'] at h'

theorem nodup_map_keep {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, ¬ InternalDart Delta.toCombMap R.faces d) (hnodup : l.Nodup) :
    (l.map R.keep).Nodup :=
  List.Nodup.map_on (fun x hx y hy hxy =>
    (R.val_keep (hl x hx)).symm.trans ((congrArg R.val hxy).trans
      (R.val_keep (hl y hy)))) hnodup

/-! ## Edge reversal, face rotation, faces -/

theorem alpha_keep {d : Delta.toCombMap.Dart}
    (hd : ¬ InternalDart Delta.toCombMap R.faces d) :
    R.diagram.toCombMap.alpha (R.keep d) = R.keep (Delta.toCombMap.alpha d) := by
  apply R.val_injective
  rw [R.val_alpha, R.val_keep hd, R.val_keep (R.not_internal_alpha hd)]

theorem facePerm_keep {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ∉ R.faces) :
    R.diagram.toCombMap.facePerm (R.keep d) = R.keep (Delta.toCombMap.facePerm d) := by
  have hnot := R.not_internal_of_faceOf_not_mem hd
  have hperm : Delta.toCombMap.faceOf (Delta.toCombMap.facePerm d) ∉ R.faces := by
    rw [Delta.toCombMap.faceOf_facePerm]
    exact hd
  have hx : Delta.toCombMap.faceOf (R.val (R.keep d)) ∉ R.faces := by
    rw [R.val_keep hnot]
    exact hd
  apply R.val_injective
  rw [R.val_facePerm _ hx, R.val_keep hnot,
    R.val_keep (R.not_internal_of_faceOf_not_mem hperm)]

theorem faceOf_keep {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ∉ R.faces) :
    R.diagram.toCombMap.faceOf (R.keep d) = R.kept (Delta.toCombMap.faceOf d) hd := by
  have hnot := R.not_internal_of_faceOf_not_mem hd
  have hx : Delta.toCombMap.faceOf (R.val (R.keep d)) ∉ R.faces := by
    rw [R.val_keep hnot]
    exact hd
  rw [R.faceOf_val_not_mem _ hx]
  exact R.kept_congr hx hd (by rw [R.val_keep hnot])

theorem faceOf_keep_of_mem {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ∈ R.faces)
    (hnot : ¬ InternalDart Delta.toCombMap R.faces d) :
    R.diagram.toCombMap.faceOf (R.keep d) = R.merged := by
  refine R.faceOf_val_mem _ ?_
  rw [R.val_keep hnot]
  exact hd

/-! ## Face sets avoiding the region -/

open scoped Classical in
/-- The image of a face set under the face map of the collapse. -/
noncomputable def faceSet (s : Finset Delta.toCombMap.Face) :
    Finset R.diagram.toCombMap.Face :=
  s.image R.face

open scoped Classical in
theorem mem_faceSet {s : Finset Delta.toCombMap.Face} {F : R.diagram.toCombMap.Face} :
    F ∈ R.faceSet s ↔ ∃ g ∈ s, R.face g = F := by
  unfold faceSet
  exact Finset.mem_image

theorem kept_mem_faceSet_iff {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    {g : Delta.toCombMap.Face} (hg : g ∉ R.faces) : R.kept g hg ∈ R.faceSet s ↔ g ∈ s := by
  rw [R.mem_faceSet]
  constructor
  · rintro ⟨g', hg's, hmap⟩
    rw [R.face_of_not_mem (Finset.disjoint_left.mp hs hg's)] at hmap
    rw [← R.kept_inj hmap]
    exact hg's
  · intro hgs
    exact ⟨g, hgs, R.face_of_not_mem hg⟩

theorem merged_not_mem_faceSet {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces) :
    R.merged ∉ R.faceSet s := by
  rw [R.mem_faceSet]
  rintro ⟨g, hgs, hmap⟩
  rw [R.face_of_not_mem (Finset.disjoint_left.mp hs hgs)] at hmap
  exact R.kept_ne_merged _ _ hmap

theorem faceOf_keep_mem_faceSet_iff {s : Finset Delta.toCombMap.Face}
    (hs : Disjoint s R.faces) {d : Delta.toCombMap.Dart}
    (hd : ¬ InternalDart Delta.toCombMap R.faces d) :
    R.diagram.toCombMap.faceOf (R.keep d) ∈ R.faceSet s ↔ Delta.toCombMap.faceOf d ∈ s := by
  by_cases hmem : Delta.toCombMap.faceOf d ∈ R.faces
  · rw [R.faceOf_keep_of_mem hmem hd]
    exact ⟨fun h => (R.merged_not_mem_faceSet hs h).elim,
      fun h => (Finset.disjoint_left.mp hs h hmem).elim⟩
  · rw [R.faceOf_keep hmem, R.kept_mem_faceSet_iff hs hmem]

/-! ## Carriers -/

theorem cellDarts_not_internal (i : Fin Delta.rCellCount) {d : Delta.toCombMap.Dart}
    (hd : d ∈ cellDarts Delta i) : ¬ InternalDart Delta.toCombMap R.faces d := by
  apply R.not_internal_of_faceOf_not_mem
  rw [((Delta.faceBoundary _).mem_iff d).mp hd]
  exact R.cells_avoid _ (Embedded.cell_mem Delta i)

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
  apply List.map_injective_iff.mpr R.val_injective
  rw [R.map_keep_val fun d hd => R.cellDarts_not_internal i hd]
  change (R.diagram.faceBoundary
      (Embedded.cell R.diagram (R.cellMap.indexEquiv i)).face).darts.map R.val =
    (Delta.faceBoundary (Embedded.cell Delta i).face).darts
  rw [R.cell_face_eq i]
  exact R.faceBoundary_kept_map_val _ _

theorem outerDarts_eq : outerDarts R.diagram = (outerDarts Delta).map R.keep := by
  apply List.map_injective_iff.mpr R.val_injective
  rw [R.map_keep_val fun d hd => R.outerDarts_not_internal hd]
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
        rw [R.outerFace_eq, R.faceBoundary_kept_map_val]

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
  change (l.map R.keep).map R.diagram.label = l.map Delta.label
  rw [List.map_map]
  exact List.map_congr_left fun d hd => congrArg Delta.label (R.val_keep (hl d hd))

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
