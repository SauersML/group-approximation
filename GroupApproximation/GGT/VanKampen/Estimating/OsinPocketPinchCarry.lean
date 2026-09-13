import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSplitWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket face set across a vertex splitting inside it

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pocket face set in walk order may pass twice through a vertex and
turn there across the other passage.  A vertex splitting (`PinchSplit.Input.diagram`) at two
darts whose corners lie in the face set merges two faces of the face set.  A face then lies in the
image face set exactly when it lay in the face set, so the boundary darts do not change, and the
pocket face set transports by the identity on darts, with the same boundary cycle, arcs and sides.

* `PinchSplit.Input.Inside`: both merged faces lie in the face set.
* `PinchSplit.Input.kept_mem_faceSet_iff_of_inside`, `faceOf_mem_faceSet_iff_of_inside` and
  `isBoundaryDart_iff_of_inside`: faces and boundary darts across the split.
* `PinchSplit.Input.transportBoundaryCycleInside`: the boundary cycle after the split.
* `PocketFaceSet.pinchSplitInside`: the transported pocket face set.
* `PocketFaceSet.pinchSplitInside_closedWalk`: walk order survives when each turn runs along vertex
  rotation, in one direction or the other, without meeting a split dart before its end.
* `PocketFaceSet.pinchSplitInside_repeatedVisits_lt` and `_of_stretch`: the repeated visits drop
  when two darts of the boundary cycle land on the new vertices of `x` and `y`.
* `PocketFaceSet.exists_pinchStep_of_inside`: the conclusion of `PocketPinchStepStatement` for
  such a split.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace PinchSplit.Input

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)

/-! ## Face sets holding both pinch faces -/

/-- A face set holding both pinch faces. -/
abbrev Inside (s : Finset Delta.toCombMap.Face) : Prop := I.leftFace ∈ s ∧ I.rightFace ∈ s

/-- **A face lies in the image of a face set holding both pinch faces exactly when it lay in the
face set.** -/
theorem kept_mem_faceSet_iff_of_inside {s : Finset Delta.toCombMap.Face} (hs : I.Inside s)
    {g : Delta.toCombMap.Face} : I.kept g ∈ I.faceSet s ↔ g ∈ s := by
  refine ⟨fun h => ?_, I.kept_mem_faceSet⟩
  by_cases hl : g = I.leftFace
  · subst hl
    exact hs.1
  · by_cases hr : g = I.rightFace
    · subst hr
      exact hs.2
    · obtain ⟨g', hg', heq⟩ := Finset.mem_image.mp h
      rw [I.kept_inj hl hr heq.symm]
      exact hg'

/-- **A dart is based in the image of `s` exactly when it was based in `s`.** -/
theorem faceOf_mem_faceSet_iff_of_inside {s : Finset Delta.toCombMap.Face} (hs : I.Inside s)
    (d : Delta.toCombMap.Dart) :
    I.diagram.toCombMap.faceOf d ∈ I.faceSet s ↔ Delta.toCombMap.faceOf d ∈ s := by
  rw [I.diagram_faceOf]
  exact I.kept_mem_faceSet_iff_of_inside hs

theorem isBoundaryDart_iff_of_inside {s : Finset Delta.toCombMap.Face} (hs : I.Inside s)
    (d : Delta.toCombMap.Dart) :
    IsBoundaryDart I.diagram (I.faceSet s) d ↔ IsBoundaryDart Delta s d := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(I.faceOf_mem_faceSet_iff_of_inside hs d).mp h1,
      fun h => h2 ((I.faceOf_mem_faceSet_iff_of_inside hs (Delta.toCombMap.alpha d)).mpr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(I.faceOf_mem_faceSet_iff_of_inside hs d).mpr h1,
      fun h => h2 ((I.faceOf_mem_faceSet_iff_of_inside hs (Delta.toCombMap.alpha d)).mp h)⟩

/-- **The boundary cycle of a face set holding both pinch faces, after the split.** -/
noncomputable def transportBoundaryCycleInside {s : Finset Delta.toCombMap.Face}
    (hs : I.Inside s) (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s) :
    Surgery.MapCollapse.BoundaryCycle I.diagram.toCombMap (I.faceSet s) where
  cycle := B.cycle
  cycle_nonempty := B.cycle_nonempty
  cycle_nodup := B.cycle_nodup
  cycle_mem_iff := fun d =>
    (B.cycle_mem_iff d).trans (I.isBoundaryDart_iff_of_inside hs d).symm

theorem transportBoundaryCycleInside_cycle {s : Finset Delta.toCombMap.Face} (hs : I.Inside s)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s) :
    (I.transportBoundaryCycleInside hs B).cycle = B.cycle :=
  rfl

/-! ## Turns -/

/-- **A stretch that avoids the split darts, in one direction or the other, stays in one vertex
after the split.** -/
theorem vertexOf_eq_of_stretchAvoids_or {d e : Delta.toCombMap.Dart}
    (h : I.StretchAvoids d e ∨ I.StretchAvoids e d) :
    I.diagram.toCombMap.vertexOf d = I.diagram.toCombMap.vertexOf e :=
  h.elim I.vertexOf_eq_of_stretchAvoids fun h' => (I.vertexOf_eq_of_stretchAvoids h').symm

end PinchSplit.Input

open Embedded

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
  [DecidableEq X.toCombMap.Dart] {lo hi : ℕ}

/-! ## The transported pocket face set -/

/-- **The pocket face set after a vertex splitting** at a pinch whose two faces lie in the face
set: the image face set, the same cells through the order-preserving cell map, and the same
boundary cycle, arcs and sides. -/
noncomputable def pinchSplitInside (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces) : PocketFaceSet D eps I.diagram lo hi where
  faces := I.faceSet K.faces
  outerFace_not_mem := by
    rw [I.diagram_outerFace]
    exact fun h => K.outerFace_not_mem ((I.kept_mem_faceSet_iff_of_inside hs).mp h)
  source := I.cellMap.indexEquiv K.source
  source_not_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact fun h => K.source_not_mem ((I.kept_mem_faceSet_iff_of_inside hs).mp h)
  kept := I.cellMap.indexEquiv K.kept
  kept_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact (I.kept_mem_faceSet_iff_of_inside hs).mpr K.kept_mem
  sourceArc := K.sourceArc.mapTo id (I.cellDarts_eq K.source)
  targetArc := K.targetArc.mapTo id I.outerDarts_eq
  firstSide := K.firstSide
  secondSide := K.secondSide
  boundary := I.transportBoundaryCycleInside hs K.boundary
  decomposition := by
    have h1 : (K.sourceArc.mapTo id (I.cellDarts_eq K.source)).darts = K.sourceArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    have h2 : (K.targetArc.mapTo id I.outerDarts_eq).darts = K.targetArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    exact K.decomposition.trans (congrArg₂ (fun (a b : List X.toCombMap.Dart) =>
      K.firstSide ++ invDarts X a ++ K.secondSide ++ b) h1.symm h2.symm)
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := K.secondSide_norm_le
  lo_le := by
    rw [CyclicArc.mapTo_start]
    exact K.lo_le
  le_hi := by
    rw [CyclicArc.mapTo_start, CyclicArc.mapTo_length]
    exact K.le_hi

theorem pinchSplitInside_faces (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces) : (K.pinchSplitInside I hs).faces = I.faceSet K.faces :=
  rfl

theorem pinchSplitInside_source (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces) :
    (K.pinchSplitInside I hs).source = I.cellMap.indexEquiv K.source :=
  rfl

theorem pinchSplitInside_kept (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces) : (K.pinchSplitInside I hs).kept = I.cellMap.indexEquiv K.kept :=
  rfl

/-- **The boundary cycle is unchanged.** -/
theorem pinchSplitInside_boundary_cycle (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) :
    (K.pinchSplitInside I hs).boundary.cycle = K.boundary.cycle :=
  rfl

theorem pinchSplitInside_firstSide (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces) : (K.pinchSplitInside I hs).firstSide = K.firstSide :=
  rfl

theorem pinchSplitInside_secondSide (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces) : (K.pinchSplitInside I hs).secondSide = K.secondSide :=
  rfl

theorem pinchSplitInside_sourceArc_darts (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) :
    (K.pinchSplitInside I hs).sourceArc.darts = K.sourceArc.darts :=
  (K.sourceArc.mapTo_darts id (I.cellDarts_eq K.source)).trans (List.map_id _)

theorem pinchSplitInside_targetArc_darts (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) :
    (K.pinchSplitInside I hs).targetArc.darts = K.targetArc.darts :=
  (K.targetArc.mapTo_darts id I.outerDarts_eq).trans (List.map_id _)

theorem pinchSplitInside_targetArc_start (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) :
    (K.pinchSplitInside I hs).targetArc.start.1 = K.targetArc.start.1 :=
  K.targetArc.mapTo_start id I.outerDarts_eq

/-! ## Walk order and repeated visits -/

/-- **The split pocket is in walk order** when each turn of the boundary cycle, and the closing
turn, runs along vertex rotation in one direction or the other without meeting a split dart
before its end. -/
theorem pinchSplitInside_closedWalk (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e =>
      I.StretchAvoids (X.toCombMap.alpha d) e ∨ I.StretchAvoids e (X.toCombMap.alpha d))
    (hcloses :
      I.StretchAvoids (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
          (K.boundary.cycle.head K.boundary.cycle_nonempty) ∨
        I.StretchAvoids (K.boundary.cycle.head K.boundary.cycle_nonempty)
          (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))) :
    (K.pinchSplitInside I hs).ClosedWalk :=
  ⟨hchain.imp fun _ _ h => I.vertexOf_eq_of_stretchAvoids_or h,
    I.vertexOf_eq_of_stretchAvoids_or hcloses⟩

/-- **The split lowers the repeated visits** when two darts of the boundary cycle land on the new
vertices of `x` and `y`. -/
theorem pinchSplitInside_repeatedVisits_lt (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) {e₁ e₂ : X.toCombMap.Dart}
    (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle)
    (hx : I.diagram.toCombMap.vertexOf e₁ = I.diagram.toCombMap.vertexOf I.x)
    (hy : I.diagram.toCombMap.vertexOf e₂ = I.diagram.toCombMap.vertexOf I.y) :
    (K.pinchSplitInside I hs).repeatedVisits < K.repeatedVisits := by
  have hne : I.diagram.toCombMap.vertexOf e₁ ≠ I.diagram.toCombMap.vertexOf e₂ := fun h =>
    I.vertexOf_x_ne_y (hx.symm.trans (h.trans hy))
  have heq : X.toCombMap.vertexOf e₁ = X.toCombMap.vertexOf e₂ :=
    (I.vertexOf_eq_of_diagram hx).trans
      (((X.toCombMap.vertexOf_eq_iff I.x I.y).mpr I.same_vertex).trans
        (I.vertexOf_eq_of_diagram hy).symm)
  unfold PocketFaceSet.repeatedVisits
  exact length_sub_card_toFinset_map_lt I.diagram.toCombMap.vertexOf I.vertexProj
    X.toCombMap.vertexOf I.vertexProj_vertexOf he₁ he₂ hne heq

/-- **The split lowers the repeated visits**, from stretches of vertex rotation: one dart of the
boundary cycle runs into `x` without passing `y`, and another runs into `y` without passing
`x`. -/
theorem pinchSplitInside_repeatedVisits_lt_of_stretch (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) {e₁ e₂ : X.toCombMap.Dart}
    (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle) {n₁ n₂ : ℕ}
    (hn₁ : (X.toCombMap.sigma ^ n₁) e₁ = I.x)
    (hy₁ : ∀ i ≤ n₁, (X.toCombMap.sigma ^ i) e₁ ≠ I.y)
    (hn₂ : (X.toCombMap.sigma ^ n₂) e₂ = I.y)
    (hx₂ : ∀ i ≤ n₂, (X.toCombMap.sigma ^ i) e₂ ≠ I.x) :
    (K.pinchSplitInside I hs).repeatedVisits < K.repeatedVisits :=
  K.pinchSplitInside_repeatedVisits_lt I hs he₁ he₂
    ((I.diagram.toCombMap.vertexOf_eq_iff e₁ I.x).mpr (I.sameCycle_x_of_stretch hn₁ hy₁))
    ((I.diagram.toCombMap.vertexOf_eq_iff e₂ I.y).mpr (I.sameCycle_y_of_stretch hn₂ hx₂))

/-! ## The step -/

/-- **One step of the pinch at a split inside the face set.**  A pocket face set on a diagram
whose labels are letters, split at two darts whose faces lie in the face set, with every turn kept
on one new vertex and two darts of the boundary cycle on the new vertices of `x` and `y`, has an
O-equivalent copy whose labels are letters, with a pocket face set in walk order and fewer
repeated visits: the conclusion of `PocketPinchStepStatement`. -/
theorem exists_pinchStep_of_inside
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X) (hs : I.Inside K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e =>
      I.StretchAvoids (X.toCombMap.alpha d) e ∨ I.StretchAvoids e (X.toCombMap.alpha d))
    (hcloses :
      I.StretchAvoids (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
          (K.boundary.cycle.head K.boundary.cycle_nonempty) ∨
        I.StretchAvoids (K.boundary.cycle.head K.boundary.cycle_nonempty)
          (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty)))
    {e₁ e₂ : X.toCombMap.Dart} (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle)
    (hx : I.diagram.toCombMap.vertexOf e₁ = I.diagram.toCombMap.vertexOf I.x)
    (hy : I.diagram.toCombMap.vertexOf e₂ = I.diagram.toCombMap.vertexOf I.y) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits :=
  ⟨I.diagram, K.pinchSplitInside I hs, ⟨I.oEquivalent⟩,
    I.label_isLetter (symmetricLabelAlphabet D) hlabel,
    K.pinchSplitInside_closedWalk I hs hchain hcloses,
    K.pinchSplitInside_repeatedVisits_lt I hs he₁ he₂ hx hy⟩

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.Inside
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.kept_mem_faceSet_iff_of_inside
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.faceOf_mem_faceSet_iff_of_inside
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.isBoundaryDart_iff_of_inside
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.transportBoundaryCycleInside
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.transportBoundaryCycleInside_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.vertexOf_eq_of_stretchAvoids_or
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_source
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_kept
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_boundary_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_firstSide
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_secondSide
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_sourceArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_targetArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_targetArc_start
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_repeatedVisits_lt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplitInside_repeatedVisits_lt_of_stretch
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_pinchStep_of_inside
