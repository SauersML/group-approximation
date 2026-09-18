import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSideStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveStepCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-50: corner turns are forward steps of the curve

Lane gl-p07-50.  Certifies no printed sentence on its own.

Let `(x, y)` be consecutive in a rotation of `l = invDarts X ow`, with a corner turn at `y`
(`WitnessStepCornerTurn`).  The filters are no-ops (`WitnessStepCornerFace.lean`), so each kind of
corner turn is a filtered turn of an earlier lane.
* Along `b.sideFrom i`: `y ∈ B̄` (`witnessStepCorner_mem_sideBWord`), then
  `witnessStepSide_step_of_turnB`.
* Along `a.sideFrom j`: `y ∈ Ā` (`witnessStepCorner_mem_sideAWord`), `α g ∉ Ḡ₂`
  (`witnessStepCorner_alpha_not_mem_invG₂`) and `g ∉ b.sideFrom i` (disjoint regions), then
  `witnessStepSide_step_of_turnA`.
* Along `G₂`: `y ∉ Ḡ₁` (`witnessStepCorner_not_mem_invG₁_of_mem_G₂`), then
  `witnessStep_step_of_cellTurn₂`.
* Wrap-around: the second disjunct of `StepNext`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section CornerStep

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A corner turn at `y` is a forward step of the curve.**  The faces of `Π_i` and `Π_j` are
off both regions, the regions are disjoint, `i ≠ j`, and the enclosed faces `F` are off both
regions. -/
theorem witnessStepCorner_step_of_cornerTurn {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    (hlab : ∀ e ∈ invDarts X ow, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i)
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFb : ∀ f ∈ F, f ∉ b.1)
    (hij : i ≠ j) (hab : Disjoint a.1 b.1)
    (hai : (cell X i).face ∉ a.1) (haj : (cell X j).face ∉ a.1)
    (hbi : (cell X i).face ∉ b.1) (hbj : (cell X j).face ∉ b.1)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (h : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hc : WitnessStepCornerTurn a b G₁ G₂ ow y) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y := by
  unfold WitnessStepCornerTurn at hc
  rcases hc with ⟨p, q, g, hg, hS⟩ | ⟨p, q, g, hg, hS⟩ | ⟨p, q, g, hg, hG⟩ | hwrap
  · have hy : X.toCombMap.alpha y ∈ b.sideFrom i := by
      rw [hS]
      simp
    exact witnessStepSide_step_of_turnB E hnb hlab hFb h hS hg
      (witnessStepCorner_mem_sideBWord hy hbi hbj)
  · have hy : X.toCombMap.alpha y ∈ a.sideFrom j := by
      rw [hS]
      simp
    have hgS : g ∈ a.sideFrom j := by
      rw [hS]
      simp
    exact witnessStepSide_step_of_turnA E hnb hFa h hS hg
      (witnessStepCorner_mem_sideAWord hab hy hai haj)
      (witnessStepCorner_alpha_not_mem_invG₂ hgS haj)
      (witnessStepCorner_not_mem_sideFrom_of_disjoint hab j i hgS)
  · have hy : X.toCombMap.alpha y ∈ G₂.darts := by
      rw [hG]
      simp
    exact witnessStep_step_of_cellTurn₂ E hlab h hG hg
      (witnessStepCorner_not_mem_invG₁_of_mem_G₂ hij hy)
  · unfold WitnessCurveSublistList.StepNext
    exact Or.inr hwrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCorner_step_of_cornerTurn

end CornerStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
