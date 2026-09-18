import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepCell
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipVertex
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchOffFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassCells
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-57: every step of the walk is a curve step or an off-lobe pinch

Lane gl-p07-57.  Certifies no printed sentence on its own.  NOT COMPILED.

`witnessStepPinchArc_classify`: **per step** of `l = invDarts X ow`, the case split that the chain
`WitnessCurveSublistStep ⇐ StepResidual ⇐ Side ⇐ Block ⇐ Corner ⇐ Skip ⇐ Pinch ⇐ PinchOff` runs at
the level of statements.  A step `(x, y)` is a forward `StepNext` of the curve `w`, or it has no
cell, side, block-order or corner turn and is an off-lobe pinch.  The proof reuses the proved
turn lemmas of lanes gl-p07-40 to gl-p07-53, one per case, on the same data.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section ArcClassify

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Turn classification of one step.**  Under the pocket premises, a step `(x, y)` of the
inverted enclosing walk is a forward `StepNext` of the curve, or an off-lobe pinch with no cell,
side, block-order or corner turn. -/
theorem witnessStepPinchArc_classify {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {ow : List X.toCombMap.Dart}
    (hij : i ≠ j) (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (hab : Disjoint a.1 b.1)
    (hai₁ : 0 < (a.cellArcList i).length) (haj₁ : 0 < (a.cellArcList j).length)
    (hbi₁ : 0 < (b.cellArcList i).length) (hbj₁ : 0 < (b.cellArcList j).length)
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) (hCa : c ∉ a.1) (hCb : c ∉ b.1)
    (E : EnclosedFaceSetSucc X (witnessFaces a b K c) ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c)
    (hlab : ∀ e ∈ invDarts X ow, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y ∨
      (¬ WitnessStepCellTurn G₁ G₂ ow y ∧ ¬ WitnessStepSideTurn a b G₁ G₂ ow y ∧
        ¬ WitnessStepBlockTurn a b G₁ G₂ x y ∧ ¬ WitnessStepCornerTurn a b G₁ G₂ ow y ∧
        WitnessStepPinchOffAt a b K c G₁ G₂ ow x y) := by
  have hFa : ∀ f ∈ witnessFaces a b K c, f ∉ a.1 :=
    fun f hf => not_mem_left_of_mem_witnessFaces hCa hf
  have hFb : ∀ f ∈ witnessFaces a b K c, f ∉ b.1 :=
    fun f hf => not_mem_right_of_mem_witnessFaces hCb hf
  have hcai : (cell X i).face ∉ a.1 := witnessStepCorner_cell_face_not_mem a
    (RegionCandidate.JoinsCells.source_or_target_left hai) hai₁
  have hcaj : (cell X j).face ∉ a.1 := witnessStepCorner_cell_face_not_mem a
    (RegionCandidate.JoinsCells.source_or_target_right hai) haj₁
  have hcbi : (cell X i).face ∉ b.1 := witnessStepCorner_cell_face_not_mem b
    (RegionCandidate.JoinsCells.source_or_target_left hbi) hbi₁
  have hcbj : (cell X j).face ∉ b.1 := witnessStepCorner_cell_face_not_mem b
    (RegionCandidate.JoinsCells.source_or_target_right hbi) hbj₁
  have hFi : (cell X i).face ∉ witnessFaces a b K c := fun hf =>
    PocketClass.cell_face_not_mem_sideFaces hw K.firstArc K.firstArc_pos
      (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_firstArc K hd)
      (witnessFaces_subset_sideFaces hf)
  have hFj : (cell X j).face ∉ witnessFaces a b K c := fun hf =>
    PocketClass.cell_face_not_mem_sideFaces hw K.secondArc K.secondArc_pos
      (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_secondArc K hd)
      (witnessFaces_subset_sideFaces hf)
  by_cases hcell : WitnessStepCellTurn G₁ G₂ ow y
  · left
    unfold WitnessStepCellTurn at hcell
    rcases hcell with ⟨p, q, g, hg, hG⟩ | ⟨p, q, g, hg, hG, hy1⟩
    · exact witnessStep_step_of_cellTurn₁ E hr hG hg
    · exact witnessStep_step_of_cellTurn₂ E hlab hr hG hg hy1
  by_cases hside : WitnessStepSideTurn a b G₁ G₂ ow y
  · left
    unfold WitnessStepSideTurn at hside
    rcases hside with ⟨p, q, g, hg, hS, hyB⟩ | ⟨p, q, g, hg, hS, hyA, hg2, hgb⟩
    · exact witnessStepSide_step_of_turnB E hnb hlab hFb hr hS hg hyB
    · exact witnessStepSide_step_of_turnA E hnb hFa hr hS hg hyA hg2 hgb
  by_cases hblock : WitnessStepBlockTurn a b G₁ G₂ x y
  · left
    have hyl : y ∈ invDarts X ow := (List.mem_rotate (n := n)).mp (by rw [hr]; simp)
    exact witnessStepBlock_step_of_blockTurn (witnessSublist_mem_curve (hlab y hyl)) hblock
  by_cases hcorner : WitnessStepCornerTurn a b G₁ G₂ ow y
  · left
    exact witnessStepCorner_step_of_cornerTurn E hnb hlab hFa hFb hij hab hcai hcaj hcbi hcbj hr
      hcorner
  have hskip := witnessStepSkip_skipAt E hr hcell hcorner
  unfold WitnessStepSkipAt at hskip
  rcases hskip with ⟨g, hP, hg, hv⟩ | ⟨hG1, hno⟩
  · exact Or.inr ⟨hcell, hside, hblock, hcorner,
      witnessStepPinchOff_at_of_pinchAt E hnb hFa hFb hFi hFj hG₁ hG₂ hr ⟨g, Or.inl hP, hg, hv⟩⟩
  · rcases witnessStepPinch_step_of_pieceEnd E hnb hr hlab hG1 hno hFa hFb hFi hFj hij hab
        hai hbi hai₁ haj₁ hbj₁ hcai hcaj hcbi hcbj K.firstArc hG₁ K.secondArc hG₂ with
      hstep | hpinch
    · exact Or.inl hstep
    · exact Or.inr ⟨hcell, hside, hblock, hcorner,
        witnessStepPinchOff_at_of_pinchAt E hnb hFa hFb hFi hFj hG₁ hG₂ hr hpinch⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchArc_classify

end ArcClassify

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
