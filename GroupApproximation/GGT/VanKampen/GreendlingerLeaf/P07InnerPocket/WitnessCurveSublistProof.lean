import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistRotate
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-36c: the witness curve sublist from the step residual

Lane gl-p07-36c.  This file proves `FourPieceWitness.WitnessCurveSublistNondegStatement`
(`FourBlockNondegStepStatement.lean`) from `FourPieceWitness.WitnessCurveSublistStepStatement`
(`WitnessCurveSublistStatement.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
Certifies no printed sentence on its own.

* `witnessSublist_curve_nodup`: the curve word `w` is duplicate free.  Each block is a filter of
  a duplicate-free list: `invDarts` of a cyclic arc of a cell, or of a region side.  The priority
  filter makes the blocks pairwise disjoint (`FourBlock.mem_sideAWord`, `mem_cellG2Word`,
  `mem_sideBWord`).
* `witnessSublist_mem_curve`: every dart in one of the four classes lies in `w`.  The block it
  lands in is the first class that holds, in the order `G1`, `G2`, `B`, `A`.
* `witnessCurveSublistNondeg_of_step`: `l = invDarts X outerWalk` is duplicate free
  (`EnclosedFaceSet.nodup`), and `l ⊆ w` by the step 1 label.  Then
  `WitnessCurveSublistList.exists_rotate_sublist_of_steps`, or its reverse form, applies.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section Curve

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The priority-filtered inverse pocket curve is duplicate free.** -/
theorem witnessSublist_curve_nodup (a b : RegionCandidate D eps X)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j)) :
    (witnessSublistCurve a b G₁ G₂).Nodup := by
  have h1 : (invDarts X G₁.darts).Nodup :=
    Embedded.invDarts_nodup (G₁.darts_nodup (Embedded.cellDarts_nodup X i))
  have h2 : (invDarts X G₂.darts).Nodup :=
    Embedded.invDarts_nodup (G₂.darts_nodup (Embedded.cellDarts_nodup X j))
  have hA : (FourBlock.sideAWord a b G₁ G₂).Nodup := by
    unfold FourBlock.sideAWord
    exact (Embedded.invDarts_nodup (a.sideFrom_nodup j)).filter _
  have hG : (FourBlock.cellG2Word G₁ G₂).Nodup := by
    unfold FourBlock.cellG2Word
    exact h2.filter _
  have hB : (FourBlock.sideBWord b G₁ G₂).Nodup := by
    unfold FourBlock.sideBWord
    exact (Embedded.invDarts_nodup (b.sideFrom_nodup i)).filter _
  unfold witnessSublistCurve
  refine List.nodup_append.mpr
    ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨h1, hA, ?_⟩, hG, ?_⟩, hB, ?_⟩
  · intro e he e' he' hee
    subst hee
    exact (FourBlock.mem_sideAWord he').1 he
  · intro e he e' he' hee
    subst hee
    rcases List.mem_append.mp he with he | he
    · exact (FourBlock.mem_cellG2Word he').1 he
    · exact (FourBlock.mem_sideAWord he).2.1 (FourBlock.mem_cellG2Word he').2
  · intro e he e' he' hee
    subst hee
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact (FourBlock.mem_sideBWord he').1 he
      · exact (FourBlock.mem_sideAWord he).2.2 (FourBlock.mem_sideBWord he').2.2
    · exact (FourBlock.mem_sideBWord he').2.1 (FourBlock.mem_cellG2Word he).2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessSublist_curve_nodup

/-- **Every dart in one of the four priority classes lies in the curve word.** -/
theorem witnessSublist_mem_curve {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {e : X.toCombMap.Dart}
    (he : e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i) :
    e ∈ witnessSublistCurve a b G₁ G₂ := by
  unfold witnessSublistCurve
  by_cases h1 : e ∈ invDarts X G₁.darts
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1))
  by_cases h2 : e ∈ invDarts X G₂.darts
  · refine List.mem_append_left _ (List.mem_append_right _ ?_)
    unfold FourBlock.cellG2Word
    exact List.mem_filter.mpr ⟨h2, @decide_eq_true _ _ ⟨h1, h2⟩⟩
  by_cases hb : X.toCombMap.alpha e ∈ b.sideFrom i
  · refine List.mem_append_right _ ?_
    unfold FourBlock.sideBWord
    exact List.mem_filter.mpr ⟨(Embedded.mem_invDarts_iff _ _).mpr hb,
      @decide_eq_true _ _ ⟨h1, h2, hb⟩⟩
  have ha : X.toCombMap.alpha e ∈ a.sideFrom j := by
    rcases he with h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
    · exact absurd h hb
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  unfold FourBlock.sideAWord
  exact List.mem_filter.mpr ⟨(Embedded.mem_invDarts_iff _ _).mpr ha,
    @decide_eq_true _ _ ⟨h1, h2, hb⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessSublist_mem_curve

end Curve

/-- **Lane gl-p07-36c: the witness curve sublist residual from the local step residual.** -/
theorem witnessCurveSublistNondeg_of_step (h : WitnessCurveSublistStepStatement.{u, w, v}) :
    WitnessCurveSublistNondegStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  have hwn : (witnessSublistCurve a b G₁ G₂).Nodup := witnessSublist_curve_nodup a b G₁ G₂
  have hl : (invDarts X outerWalk).Nodup := Embedded.invDarts_nodup E.nodup
  have hsub : ∀ e ∈ invDarts X outerWalk, e ∈ witnessSublistCurve a b G₁ G₂ :=
    fun e he => witnessSublist_mem_curve (hlab e he)
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁ hG₁ G₂
      hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab with hstep | hstep
  · obtain ⟨n, hn⟩ := WitnessCurveSublistList.exists_rotate_sublist_of_steps hwn hl hsub hstep
    exact ⟨n, Or.inl hn⟩
  · obtain ⟨n, hn⟩ :=
      WitnessCurveSublistList.exists_rotate_reverse_sublist_of_steps hwn hl hsub hstep
    exact ⟨n, Or.inr hn⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessCurveSublistNondeg_of_step

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
