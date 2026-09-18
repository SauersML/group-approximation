import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBlockStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-49: block-order turns are forward steps of the curve

Lane gl-p07-49.  Certifies no printed sentence on its own.

* `witnessStepBlock_curve_eq_append₂`: the curve word splits after its second block,
  `w = (Ḡ₁ ++ Ā) ++ (Ḡ₂' ++ B̄)`.
* `witnessStepBlock_step_of_blockTurn`: if `y ∈ w` and `(x, y)` is a block-order turn, then `x`
  comes before `y` in `w`, which is the forward form of `StepNext w l x y`, for every `l`.  In the
  case `x ∈ Ḡ₁`, `y ∉ Ḡ₁`, the membership `y ∈ w` puts `y` in the tail `Ā ++ Ḡ₂' ++ B̄`.
  In the other two cases the blocks of `x` and `y` are given, and the split after the second
  (resp. third) block does it.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section BlockStep

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The curve word splits after its second block.** -/
theorem witnessStepBlock_curve_eq_append₂ (a b : RegionCandidate D eps X)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) :
    witnessSublistCurve a b G₁ G₂ = (invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂) ++
      (FourBlock.cellG2Word G₁ G₂ ++ FourBlock.sideBWord b G₁ G₂) := by
  unfold witnessSublistCurve
  simp only [List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBlock_curve_eq_append₂

/-- **A block-order turn is a forward step of the curve.** -/
theorem witnessStepBlock_step_of_blockTurn {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {l : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hyw : y ∈ witnessSublistCurve a b G₁ G₂) (hturn : WitnessStepBlockTurn a b G₁ G₂ x y) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) l x y := by
  unfold WitnessCurveSublistList.StepNext
  refine Or.inl ?_
  unfold WitnessStepBlockTurn at hturn
  rcases hturn with ⟨hx1, hy1⟩ | ⟨hxA, hyR⟩ | ⟨hxC, hyB⟩
  · rw [witnessStep_curve_eq_append] at hyw ⊢
    have hyT : y ∈ FourBlock.sideAWord a b G₁ G₂ ++ FourBlock.cellG2Word G₁ G₂ ++
        FourBlock.sideBWord b G₁ G₂ := by
      rcases List.mem_append.mp hyw with hy | hy
      · exact absurd hy hy1
      · exact hy
    exact witnessStep_forward_of_mem_append hx1 hyT
  · rw [witnessStepBlock_curve_eq_append₂]
    have hxL : x ∈ invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ :=
      List.mem_append_right _ hxA
    have hyL : y ∈ FourBlock.cellG2Word G₁ G₂ ++ FourBlock.sideBWord b G₁ G₂ :=
      List.mem_append.mpr hyR
    exact witnessStep_forward_of_mem_append hxL hyL
  · have hxL : x ∈ invDarts X G₁.darts ++ FourBlock.sideAWord a b G₁ G₂ ++
        FourBlock.cellG2Word G₁ G₂ :=
      List.mem_append_right _ hxC
    unfold witnessSublistCurve
    exact witnessStep_forward_of_mem_append hxL hyB

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBlock_step_of_blockTurn

end BlockStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
