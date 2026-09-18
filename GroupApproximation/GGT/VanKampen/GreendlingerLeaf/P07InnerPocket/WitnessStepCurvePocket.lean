import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurveChain
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: the doubled pocket curve is a bounce chain (assembly)

Lane gl-p07-66.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

Math: see `WitnessStepCurveChain.lean`.  Split the four nonempty arcs at their corner darts,
read the four `Hop'` chains off the two arcs of `K` and the two boundary rotations, check the
four bounces, and apply `witnessStepCurve_double_chain`.  The rotation of the boundary of `a`
used is the rotation `Ā_ai · S_ai · Ā_aj · S_aj` moved on by `|Ā_ai|`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The doubled unfiltered pocket curve is a bounce chain.** -/
theorem witnessStepCurve_pocket_chain (hij : i ≠ j) {a b : RegionCandidate D eps X}
    (K : CellPocketWalk D eps X i j) (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j)
    (hab : Disjoint a.1 b.1) (hai₁ : 0 < (a.cellArcList i).length)
    (haj₁ : 0 < (a.cellArcList j).length) (hbi₁ : 0 < (b.cellArcList i).length)
    (hbj₁ : 0 < (b.cellArcList j).length) (G₁ : CyclicArc (cellDarts X i))
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (G₂ : CyclicArc (cellDarts X j))
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {Γ : List X.toCombMap.Dart}
    (hΓ : Γ = b.sideFrom i ++ G₂.darts ++ a.sideFrom j ++ G₁.darts) :
    (Γ ++ Γ).IsChain (witnessStepCurve_Rel X.toCombMap Γ) := by
  have fai := witnessStepCorner_cell_face_not_mem a hai.source_or_target_left hai₁
  have faj := witnessStepCorner_cell_face_not_mem a hai.source_or_target_right haj₁
  have fbi := witnessStepCorner_cell_face_not_mem b hbi.source_or_target_left hbi₁
  have fbj := witnessStepCorner_cell_face_not_mem b hbi.source_or_target_right hbj₁
  obtain ⟨Ub, Ua⟩ := witnessStepCurve_pocket_unique hab fai faj fbi fbj G₁ G₂ hΓ
  obtain ⟨zBi, Bi, hBi⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hbi₁)
  obtain ⟨Bj, zBj, hBj⟩ := witnessStepCurve_exists_concat hbj₁
  obtain ⟨zAj, Aj, hAj⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos haj₁)
  obtain ⟨Ai, zAi, hAi⟩ := witnessStepCurve_exists_concat hai₁
  have mBi : zBi ∈ b.cellArcList i := by rw [hBi]; simp
  have mBj : zBj ∈ b.cellArcList j := by rw [hBj]; simp
  have mAj : zAj ∈ a.cellArcList j := by rw [hAj]; simp
  have mAi : zAi ∈ a.cellArcList i := by rw [hAi]; simp
  obtain ⟨nb, hnb⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hbi
  obtain ⟨na, hna⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hai
  have hna' : a.2.boundary.cycle.rotate na = invDarts X (a.cellArcList i) ++
      (a.sideFrom i ++ invDarts X (a.cellArcList j) ++ a.sideFrom j) := by
    rw [hna]
    simp only [List.append_assoc]
  have hSb := witnessStepCurve_chain_of_boundary b Ub (n := nb) (s := invDarts X Bi)
    (l := X.toCombMap.alpha zBi :: (b.sideFrom i ++ [X.toCombMap.alpha zBj]))
    (t := invDarts X Bj ++ b.sideFrom j) (by
      rw [hnb, hBi, hBj, witnessStepPinch_invDarts_cons, witnessStepPinch_invDarts_concat]
      simp)
  have hS2 := witnessStepCurve_chain_of_arc (Γ := Γ) K.secondArc (s := Bj)
    (l := zBj :: (G₂.darts ++ [zAj])) (t := Aj) (by rw [hG₂, hBj, hAj]; simp)
  have hSa := witnessStepCurve_chain_of_boundary a Ua
    (n := na + (invDarts X (a.cellArcList i)).length) (s := a.sideFrom i ++ invDarts X Aj)
    (l := X.toCombMap.alpha zAj :: (a.sideFrom j ++ [X.toCombMap.alpha zAi]))
    (t := invDarts X Ai) (by
      rw [← List.rotate_rotate, hna', List.rotate_append_length_eq, hAi, hAj,
        witnessStepPinch_invDarts_concat, witnessStepPinch_invDarts_cons]
      simp)
  have hS1 := witnessStepCurve_chain_of_arc (Γ := Γ) K.firstArc (s := Ai)
    (l := zAi :: (G₁.darts ++ [zBi])) (t := Bi) (by rw [hG₁, hAi, hBi]; simp)
  have nd₁ : (a.cellArcList i ++ G₁.darts ++ b.cellArcList i).Nodup := by
    rw [← hG₁]
    exact K.firstArc.darts_nodup (Embedded.cellDarts_nodup X i)
  have nd₂ : (b.cellArcList j ++ G₂.darts ++ a.cellArcList j).Nodup := by
    rw [← hG₂]
    exact K.secondArc.darts_nodup (Embedded.cellDarts_nodup X j)
  have h₁ := witnessStepCurve_bounce_b hΓ (witnessStepCurve_bounce hij hbi hab.symm (k := i)
    (k₁ := i) j (Or.inl rfl) hbi.source_or_target_left (Or.inl rfl) fbi fbj fai G₁ G₂ mBi
    (witnessStepCurve_nodup_three nd₁ (Or.inr mBi))
    (witnessStepCurve_not_mem_other_arc b hij hbi.source_or_target_left G₂ mBi))
  have h₂ := witnessStepCurve_bounce_b hΓ (witnessStepCurve_bounce hij hbi hab.symm (k := j)
    (k₁ := i) j (Or.inr rfl) hbi.source_or_target_right (Or.inl rfl) fbi fbj faj G₁ G₂ mBj
    (witnessStepCurve_not_mem_other_arc b (Ne.symm hij) hbi.source_or_target_right G₁ mBj)
    (witnessStepCurve_nodup_three nd₂ (Or.inl mBj)))
  have h₃ := witnessStepCurve_bounce_a hΓ (witnessStepCurve_bounce hij hai hab (k := j)
    (k₁ := j) i (Or.inr rfl) hai.source_or_target_right (Or.inr rfl) fai faj fbj G₁ G₂ mAj
    (witnessStepCurve_not_mem_other_arc a (Ne.symm hij) hai.source_or_target_right G₁ mAj)
    (witnessStepCurve_nodup_three nd₂ (Or.inr mAj)))
  have h₄ := witnessStepCurve_bounce_a hΓ (witnessStepCurve_bounce hij hai hab (k := i)
    (k₁ := j) i (Or.inl rfl) hai.source_or_target_left (Or.inr rfl) fai faj fbi G₁ G₂ mAi
    (witnessStepCurve_nodup_three nd₁ (Or.inl mAi))
    (witnessStepCurve_not_mem_other_arc a hij hai.source_or_target_left G₂ mAi))
  exact witnessStepCurve_double_chain (z₁ := zBi) (z₂ := zBj) (z₃ := zAj) (z₄ := zAi) hΓ
    hSb hS2 hSa hS1 h₁ h₂ h₃ h₄

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_pocket_chain

end Pocket

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
