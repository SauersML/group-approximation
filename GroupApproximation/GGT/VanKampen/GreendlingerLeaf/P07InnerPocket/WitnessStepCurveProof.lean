import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurvePocket
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSubStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: proof of the curve successor residual

Lane gl-p07-66.  Proves `witnessStepSub_CurveSuccStatement` (the residual of lane gl-p07-65),
hence `witnessStepLobe_SublistStatement`.  Certifies no printed sentence on its own.
NOT COMPILED: authored without running Lean.

Math.
1. The faces of `Π_i`, `Π_j` are off `a` and `b` (their arcs are nonempty), and `a`, `b` are
   disjoint, so the three priority filters of `witnessSublistCurve a b G₁ G₂` remove nothing:
   the curve is `w = Γ.reverse.map α` with `Γ = b.sideFrom i ++ G₂ ++ a.sideFrom j ++ G₁`
   (`witnessStepCurve_curve_eq`).
2. `Γ ++ Γ` is a bounce chain (`witnessStepCurve_pocket_chain`): consecutive darts of `Γ` are
   joined by vertex rotations avoiding `Γ` and its reverses, and at the four corners the
   rotation passes through a corner dart that bounces (it and its reverse are off `Γ`).
3. A doubled bounce chain makes `w` a cyclic successor walk of the mirror `(α, σ⁻¹)`
   (`witnessStepCurve_succ_of_chain`).
Only the pocket premises used: `i ≠ j`, the two joins, disjointness, the four positive arc
lengths and the two arc decompositions.  The labels, relator lengths, the sides of `K`,
noncrossing, the exterior face and the two Euler equalities are not needed.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section CurveEq

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The priority filters of the pocket curve remove nothing.** -/
theorem witnessStepCurve_curve_eq (hij : i ≠ j) {a b : RegionCandidate D eps X}
    (hab : Disjoint a.1 b.1) (hai : (cell X i).face ∉ a.1) (haj : (cell X j).face ∉ a.1)
    (hbi : (cell X i).face ∉ b.1) (hbj : (cell X j).face ∉ b.1)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) :
    witnessSublistCurve a b G₁ G₂ =
      (b.sideFrom i ++ G₂.darts ++ a.sideFrom j ++ G₁.darts).reverse.map X.toCombMap.alpha := by
  have hA : FourBlock.sideAWord a b G₁ G₂ = invDarts X (a.sideFrom j) := by
    unfold FourBlock.sideAWord
    refine List.filter_eq_self.mpr fun e he => ?_
    have hα := witnessStepCorner_alpha_mem_of_mem_invDarts he
    exact @decide_eq_true _ (_)
      ⟨witnessStepCorner_not_mem_invArc_of_mem_sideFrom a j hai G₁ hα,
        witnessStepCorner_not_mem_invArc_of_mem_sideFrom a j haj G₂ hα,
        witnessStepCorner_not_mem_sideFrom_of_disjoint hab j i hα⟩
  have hG : FourBlock.cellG2Word G₁ G₂ = invDarts X G₂.darts := by
    unfold FourBlock.cellG2Word
    refine List.filter_eq_self.mpr fun e he => ?_
    exact @decide_eq_true _ (_) ⟨witnessStepCorner_not_mem_invG₁_of_mem_G₂ hij
      (witnessStepCorner_alpha_mem_of_mem_invDarts he), he⟩
  have hB : FourBlock.sideBWord b G₁ G₂ = invDarts X (b.sideFrom i) := by
    unfold FourBlock.sideBWord
    refine List.filter_eq_self.mpr fun e he => ?_
    have hα := witnessStepCorner_alpha_mem_of_mem_invDarts he
    exact @decide_eq_true _ (_)
      ⟨witnessStepCorner_not_mem_invArc_of_mem_sideFrom b i hbi G₁ hα,
        witnessStepCorner_not_mem_invArc_of_mem_sideFrom b i hbj G₂ hα, hα⟩
  unfold witnessSublistCurve
  rw [hA, hG, hB]
  simp [Embedded.invDarts]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_curve_eq

end CurveEq

/-- **Lane gl-p07-66: the pocket curve is a cyclic successor walk of the mirror.**  Proof of
the residual `witnessStepSub_CurveSuccStatement` of lane gl-p07-65. -/
theorem witnessStepCurve_proof : witnessStepSub_CurveSuccStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ _ _ _ _ G₁ hG₁ G₂ hG₂
    _ _ _ _ n s t x y h
  have fai := witnessStepCorner_cell_face_not_mem a hai.source_or_target_left hai₁
  have faj := witnessStepCorner_cell_face_not_mem a hai.source_or_target_right haj₁
  have fbi := witnessStepCorner_cell_face_not_mem b hbi.source_or_target_left hbi₁
  have fbj := witnessStepCorner_cell_face_not_mem b hbi.source_or_target_right hbj₁
  have hc := witnessStepCurve_pocket_chain hij K hai hbi hab hai₁ haj₁ hbi₁ hbj₁ G₁ hG₁ G₂ hG₂
    rfl
  rw [witnessStepCurve_curve_eq hij hab fai faj fbi fbj G₁ G₂] at h ⊢
  exact witnessStepCurve_succ_of_chain hc h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_proof

/-- **Lane gl-p07-66: the lobe sublist statement, outright.** -/
theorem witnessStepCurve_sublist : witnessStepLobe_SublistStatement.{u, w, v} :=
  witnessStepSub_sublist_of_curveSucc witnessStepCurve_proof

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_sublist

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
