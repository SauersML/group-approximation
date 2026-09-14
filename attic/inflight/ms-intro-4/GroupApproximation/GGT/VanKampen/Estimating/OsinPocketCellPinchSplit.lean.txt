import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchCarry
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket between two cells across a vertex splitting

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

The cell analogues of `PocketFaceSet.pinchSplit` (lane kh-cckw, `Estimating/OsinPocketPinchSplit.lean`
and `Estimating/OsinPocketPinchSplitWalk.lean`) and `PocketFaceSet.pinchSplitInside` (lane go-lemma42,
`Estimating/OsinPocketPinchCarry.lean`), over the same `PinchSplit.Input` layer.  A vertex splitting
changes only the vertex rotation, so the boundary cycle, both arcs and both sides are unchanged,
and the cells move through the order-preserving cell map.

* `CellPocketFaceSet.pinchSplit`, `pinchSplitInside`: across a splitting whose two faces avoid the
  face set, or lie in it.
* `_boundary_cycle`: the cycle is unchanged.  `_closedWalk`: walk order is kept when every turn is
  a stretch avoiding the split darts.  `_repeatedVisits_lt`, `_of_stretch`: the repeated visits drop
  when two darts of the cycle land on the two new vertices.
* `CellPocketFaceSet.exists_cellPinchStep_of_avoids`, `exists_cellPinchStep_of_inside`: the
  conclusion of `CellPocketPinchStepPosStatement` at such a splitting.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
  [DecidableEq X.toCombMap.Dart] {i j : Fin X.rCellCount}

/-! ## A splitting avoiding the face set -/

/-- **The cell pocket face set after a vertex splitting** at a pinch avoiding its faces: the image
face set, the same cells through the cell map, and the same boundary cycle, arcs and sides. -/
noncomputable def pinchSplit (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) :
    CellPocketFaceSet D eps I.diagram (I.cellMap.indexEquiv i) (I.cellMap.indexEquiv j) where
  faces := I.faceSet K.faces
  outerFace_not_mem := by
    rw [I.diagram_outerFace]
    exact fun h => K.outerFace_not_mem ((I.kept_mem_faceSet_iff hs).mp h)
  first_not_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact fun h => K.first_not_mem ((I.kept_mem_faceSet_iff hs).mp h)
  second_not_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact fun h => K.second_not_mem ((I.kept_mem_faceSet_iff hs).mp h)
  kept := I.cellMap.indexEquiv K.kept
  kept_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact (I.kept_mem_faceSet_iff hs).mpr K.kept_mem
  firstArc := K.firstArc.mapTo id (I.cellDarts_eq i)
  secondArc := K.secondArc.mapTo id (I.cellDarts_eq j)
  firstSide := K.firstSide
  secondSide := K.secondSide
  boundary := I.transportBoundaryCycle hs K.boundary
  decomposition := by
    have h1 : (K.firstArc.mapTo id (I.cellDarts_eq i)).darts = K.firstArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    have h2 : (K.secondArc.mapTo id (I.cellDarts_eq j)).darts = K.secondArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    exact K.decomposition.trans (congrArg₂ (fun (a b : List X.toCombMap.Dart) =>
      K.firstSide ++ invDarts X a ++ K.secondSide ++ invDarts X b) h1.symm h2.symm)
  firstArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.firstArc_pos
  secondArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.secondArc_pos
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := K.secondSide_norm_le

/-- **The boundary cycle is unchanged.** -/
theorem pinchSplit_boundary_cycle (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).boundary.cycle = K.boundary.cycle :=
  rfl

/-- **The split cell pocket is in walk order** when each step of the boundary cycle, and the
closing step, runs along vertex rotation without meeting a split dart before its end. -/
theorem pinchSplit_closedWalk (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.StretchAvoids (X.toCombMap.alpha d) e)
    (hcloses : I.StretchAvoids
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty)) :
    (K.pinchSplit I hs).ClosedWalk :=
  ⟨hchain.imp fun _ _ h => I.vertexOf_eq_of_stretchAvoids h,
    I.vertexOf_eq_of_stretchAvoids hcloses⟩

/-- **The split lowers the repeated visits** when two darts of the boundary cycle land on the new
vertices of `x` and `y`. -/
theorem pinchSplit_repeatedVisits_lt (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) {e₁ e₂ : X.toCombMap.Dart} (he₁ : e₁ ∈ K.boundary.cycle)
    (he₂ : e₂ ∈ K.boundary.cycle)
    (hx : I.diagram.toCombMap.vertexOf e₁ = I.diagram.toCombMap.vertexOf I.x)
    (hy : I.diagram.toCombMap.vertexOf e₂ = I.diagram.toCombMap.vertexOf I.y) :
    (K.pinchSplit I hs).repeatedVisits < K.repeatedVisits := by
  have hne : I.diagram.toCombMap.vertexOf e₁ ≠ I.diagram.toCombMap.vertexOf e₂ := fun h =>
    I.vertexOf_x_ne_y (hx.symm.trans (h.trans hy))
  have heq : X.toCombMap.vertexOf e₁ = X.toCombMap.vertexOf e₂ :=
    (I.vertexOf_eq_of_diagram hx).trans
      (((X.toCombMap.vertexOf_eq_iff I.x I.y).mpr I.same_vertex).trans
        (I.vertexOf_eq_of_diagram hy).symm)
  unfold CellPocketFaceSet.repeatedVisits
  exact length_sub_card_toFinset_map_lt I.diagram.toCombMap.vertexOf I.vertexProj
    X.toCombMap.vertexOf I.vertexProj_vertexOf he₁ he₂ hne heq

/-- **The split lowers the repeated visits**, from stretches of vertex rotation into `x` and into
`y`. -/
theorem pinchSplit_repeatedVisits_lt_of_stretch (K : CellPocketFaceSet D eps X i j)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces) {e₁ e₂ : X.toCombMap.Dart}
    (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle) {n₁ n₂ : ℕ}
    (hn₁ : (X.toCombMap.sigma ^ n₁) e₁ = I.x)
    (hy₁ : ∀ i ≤ n₁, (X.toCombMap.sigma ^ i) e₁ ≠ I.y)
    (hn₂ : (X.toCombMap.sigma ^ n₂) e₂ = I.y)
    (hx₂ : ∀ i ≤ n₂, (X.toCombMap.sigma ^ i) e₂ ≠ I.x) :
    (K.pinchSplit I hs).repeatedVisits < K.repeatedVisits :=
  K.pinchSplit_repeatedVisits_lt I hs he₁ he₂
    ((I.diagram.toCombMap.vertexOf_eq_iff e₁ I.x).mpr (I.sameCycle_x_of_stretch hn₁ hy₁))
    ((I.diagram.toCombMap.vertexOf_eq_iff e₂ I.y).mpr (I.sameCycle_y_of_stretch hn₂ hx₂))

/-- **One step of the cell pinch at a splitting avoiding the face set**: the conclusion of
`CellPocketPinchStepPosStatement`. -/
theorem exists_cellPinchStep_of_avoids
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.StretchAvoids (X.toCombMap.alpha d) e)
    (hcloses : I.StretchAvoids
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty))
    {e₁ e₂ : X.toCombMap.Dart} (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle)
    (hx : I.diagram.toCombMap.vertexOf e₁ = I.diagram.toCombMap.vertexOf I.x)
    (hy : I.diagram.toCombMap.vertexOf e₂ = I.diagram.toCombMap.vertexOf I.y) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits :=
  ⟨I.diagram, I.cellMap.indexEquiv i, I.cellMap.indexEquiv j, K.pinchSplit I hs,
    ⟨I.oEquivalent⟩, I.label_isLetter (symmetricLabelAlphabet D) hlabel,
    K.pinchSplit_closedWalk I hs hchain hcloses,
    K.pinchSplit_repeatedVisits_lt I hs he₁ he₂ hx hy⟩

/-! ## A splitting inside the face set -/

/-- **The cell pocket face set after a vertex splitting** at a pinch whose two faces lie in the face
set. -/
noncomputable def pinchSplitInside (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    (hs : I.Inside K.faces) :
    CellPocketFaceSet D eps I.diagram (I.cellMap.indexEquiv i) (I.cellMap.indexEquiv j) where
  faces := I.faceSet K.faces
  outerFace_not_mem := by
    rw [I.diagram_outerFace]
    exact fun h => K.outerFace_not_mem ((I.kept_mem_faceSet_iff_of_inside hs).mp h)
  first_not_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact fun h => K.first_not_mem ((I.kept_mem_faceSet_iff_of_inside hs).mp h)
  second_not_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact fun h => K.second_not_mem ((I.kept_mem_faceSet_iff_of_inside hs).mp h)
  kept := I.cellMap.indexEquiv K.kept
  kept_mem := by
    rw [I.cellMap.indexed_cell, I.cellMap.face_eq]
    exact (I.kept_mem_faceSet_iff_of_inside hs).mpr K.kept_mem
  firstArc := K.firstArc.mapTo id (I.cellDarts_eq i)
  secondArc := K.secondArc.mapTo id (I.cellDarts_eq j)
  firstSide := K.firstSide
  secondSide := K.secondSide
  boundary := I.transportBoundaryCycleInside hs K.boundary
  decomposition := by
    have h1 : (K.firstArc.mapTo id (I.cellDarts_eq i)).darts = K.firstArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    have h2 : (K.secondArc.mapTo id (I.cellDarts_eq j)).darts = K.secondArc.darts :=
      (CyclicArc.mapTo_darts _ _ _).trans (List.map_id _)
    exact K.decomposition.trans (congrArg₂ (fun (a b : List X.toCombMap.Dart) =>
      K.firstSide ++ invDarts X a ++ K.secondSide ++ invDarts X b) h1.symm h2.symm)
  firstArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.firstArc_pos
  secondArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.secondArc_pos
  firstSide_length_le := K.firstSide_length_le
  secondSide_length_le := K.secondSide_length_le
  firstSide_norm_le := K.firstSide_norm_le
  secondSide_norm_le := K.secondSide_norm_le

/-- **The boundary cycle is unchanged.** -/
theorem pinchSplitInside_boundary_cycle (K : CellPocketFaceSet D eps X i j)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) :
    (K.pinchSplitInside I hs).boundary.cycle = K.boundary.cycle :=
  rfl

/-- **The split cell pocket is in walk order** when each turn of the boundary cycle, and the
closing turn, runs along vertex rotation in one direction or the other without meeting a split
dart before its end. -/
theorem pinchSplitInside_closedWalk (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
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
theorem pinchSplitInside_repeatedVisits_lt (K : CellPocketFaceSet D eps X i j)
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
  unfold CellPocketFaceSet.repeatedVisits
  exact length_sub_card_toFinset_map_lt I.diagram.toCombMap.vertexOf I.vertexProj
    X.toCombMap.vertexOf I.vertexProj_vertexOf he₁ he₂ hne heq

/-- **One step of the cell pinch at a splitting inside the face set**: the conclusion of
`CellPocketPinchStepPosStatement`. -/
theorem exists_cellPinchStep_of_inside
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X) (hs : I.Inside K.faces)
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
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits :=
  ⟨I.diagram, I.cellMap.indexEquiv i, I.cellMap.indexEquiv j, K.pinchSplitInside I hs,
    ⟨I.oEquivalent⟩, I.label_isLetter (symmetricLabelAlphabet D) hlabel,
    K.pinchSplitInside_closedWalk I hs hchain hcloses,
    K.pinchSplitInside_repeatedVisits_lt I hs he₁ he₂ hx hy⟩

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplit
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplit_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplit_repeatedVisits_lt
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_cellPinchStep_of_avoids
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplitInside
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplitInside_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_cellPinchStep_of_inside
