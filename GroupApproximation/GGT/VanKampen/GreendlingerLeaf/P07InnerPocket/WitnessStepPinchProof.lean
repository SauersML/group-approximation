import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchEnd
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassCells
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-52: the skip residual from the pinch residual

Lane gl-p07-52.  Certifies no printed sentence on its own.  NOT COMPILED.

`witnessStepSkip_of_witnessStepPinch` proves `WitnessStepSkipStatement` from
`WitnessStepPinchStatement`.  Run the pinch residual on the same data.  The backward disjunct
passes through unchanged.  In the forward disjunct, a skip is either a pinch inside a piece, which
is a pinch here, or a piece end.  At a piece end, `witnessStepPinch_step_of_pieceEnd` gives the
step or a pinch across a junction, and the pinch residual gives the step at that pinch.

The face facts come from the premises:
* the witness faces are off `a` and `b` (`not_mem_left/right_of_mem_witnessFaces`);
* the faces of `Π_i` and `Π_j` are off `a` and `b` (`witnessStepCorner_cell_face_not_mem`);
* the faces of `Π_i` and `Π_j` are off the witness faces, since the witness faces lie on the side
  of `K.walk` (`witnessFaces_subset_sideFaces`) and the cells do not
  (`PocketClass.cell_face_not_mem_sideFaces` on `K.firstArc` and `K.secondArc`).

See `WitnessStepPinchStatement.lean` for the truth check and the LOUD notes: the two residuals are
logically equivalent, and the pinch one is smaller only in proof content.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section PinchProof

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The piece-end case of a skip.**  If `α y` is off `G₁` and has no successor inside a piece,
then `α y` ends `B`, `G₂` or `A`, and the pair `(x, y)` is a step of the curve or a pinch. -/
theorem witnessStepPinch_step_of_pieceEnd {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ F)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hlab : ∀ e ∈ invDarts X ow, e ∈ invDarts X G₁.darts ∨ e ∈ invDarts X G₂.darts ∨
      X.toCombMap.alpha e ∈ a.sideFrom j ∨ X.toCombMap.alpha e ∈ b.sideFrom i)
    (hG1 : X.toCombMap.alpha y ∉ G₁.darts)
    (hno : ∀ g : X.toCombMap.Dart, ¬ WitnessStepSkipPieceNext a b G₁ G₂ (X.toCombMap.alpha y) g)
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFb : ∀ f ∈ F, f ∉ b.1) (hFi : (cell X i).face ∉ F)
    (hFj : (cell X j).face ∉ F) (hij : i ≠ j) (hab : Disjoint a.1 b.1)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (hai₁ : 0 < (a.cellArcList i).length)
    (haj₁ : 0 < (a.cellArcList j).length) (hbj₁ : 0 < (b.cellArcList j).length)
    (hcai : (cell X i).face ∉ a.1) (hcaj : (cell X j).face ∉ a.1)
    (hcbi : (cell X i).face ∉ b.1) (hcbj : (cell X j).face ∉ b.1)
    (K₁ : CyclicArc (cellDarts X i))
    (hK₁ : K₁.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (K₂ : CyclicArc (cellDarts X j))
    (hK₂ : K₂.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) :
    WitnessCurveSublistList.StepNext (witnessSublistCurve a b G₁ G₂) (invDarts X ow) x y ∨
      WitnessStepPinchAt a b G₁ G₂ ow x y := by
  have hy' : y ∈ (invDarts X ow).rotate n := by
    rw [hr]
    simp
  rcases hlab y (List.mem_rotate.mp hy') with hy | hy | hy | hy
  · exact absurd (witnessStepCorner_alpha_mem_of_mem_invDarts hy) hG1
  · obtain ⟨p, hp⟩ := witnessStepSkip_eq_append_singleton
      (witnessStepCorner_alpha_mem_of_mem_invDarts hy)
      (fun g hg => hno g (Or.inr (Or.inr (Or.inl hg))))
    have hyC : y ∈ FourBlock.cellG2Word G₁ G₂ := witnessStepPinch_mem_cellG2Word
      (fun h1 => hG1 (witnessStepCorner_alpha_mem_of_mem_invDarts h1)) hy
    exact witnessStepPinch_step_of_end_G₂ E hnb hr hFa hFi hFj hij hab hai hai₁ haj₁ hcai hcaj
      K₁ hK₁ K₂ hK₂ hp hyC
  · obtain ⟨p, hp⟩ := witnessStepSkip_eq_append_singleton hy
      (fun g hg => hno g (Or.inr (Or.inr (Or.inr hg))))
    have hyA : y ∈ FourBlock.sideAWord a b G₁ G₂ :=
      witnessStepCorner_mem_sideAWord hab hy hcai hcaj
    exact witnessStepPinch_step_of_end_A E hnb hr hFa hFi hij hai hai₁ K₁ hK₁ hp hyA
  · obtain ⟨p, hp⟩ := witnessStepSkip_eq_append_singleton hy
      (fun g hg => hno g (Or.inr (Or.inl hg)))
    have hyB : y ∈ FourBlock.sideBWord b G₁ G₂ := witnessStepCorner_mem_sideBWord hy hcbi hcbj
    exact witnessStepPinch_step_of_end_B E hnb hr hFa hFb hFi hFj hij hab hai hbi hai₁ haj₁
      hbj₁ hcai hcaj K₁ hK₁ K₂ hK₂ hp hyB

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_step_of_pieceEnd

end PinchProof

/-- **Lane gl-p07-52: the skip residual from the residual at pinches.** -/
theorem witnessStepSkip_of_witnessStepPinch (h : WitnessStepPinchStatement.{u, w, v}) :
    WitnessStepSkipStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst
    hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hlab
  rcases h D eps X a b K hij hai hbi hab hai₁ haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁
      hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
      hlab with hfwd | hbwd
  · refine Or.inl fun n s t x y hr hcell hside hblock hcorner hskip => ?_
    unfold WitnessStepSkipAt at hskip
    rcases hskip with ⟨g, hP, hg, hv⟩ | ⟨hG1, hno⟩
    · exact hfwd n s t x y hr hcell hside hblock hcorner ⟨g, Or.inl hP, hg, hv⟩
    · have hFa : ∀ f ∈ witnessFaces a b K C.face, f ∉ a.1 :=
        fun f hf => not_mem_left_of_mem_witnessFaces hCa hf
      have hFb : ∀ f ∈ witnessFaces a b K C.face, f ∉ b.1 :=
        fun f hf => not_mem_right_of_mem_witnessFaces hCb hf
      have hcai : (cell X i).face ∉ a.1 := witnessStepCorner_cell_face_not_mem a
        (RegionCandidate.JoinsCells.source_or_target_left hai) hai₁
      have hcaj : (cell X j).face ∉ a.1 := witnessStepCorner_cell_face_not_mem a
        (RegionCandidate.JoinsCells.source_or_target_right hai) haj₁
      have hcbi : (cell X i).face ∉ b.1 := witnessStepCorner_cell_face_not_mem b
        (RegionCandidate.JoinsCells.source_or_target_left hbi) hbi₁
      have hcbj : (cell X j).face ∉ b.1 := witnessStepCorner_cell_face_not_mem b
        (RegionCandidate.JoinsCells.source_or_target_right hbi) hbj₁
      have hFi : (cell X i).face ∉ witnessFaces a b K C.face := fun hf =>
        PocketClass.cell_face_not_mem_sideFaces hw K.firstArc K.firstArc_pos
          (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_firstArc K hd)
          (witnessFaces_subset_sideFaces hf)
      have hFj : (cell X j).face ∉ witnessFaces a b K C.face := fun hf =>
        PocketClass.cell_face_not_mem_sideFaces hw K.secondArc K.secondArc_pos
          (fun _ hd => PocketClass.mem_walk_of_mem_invDarts_secondArc K hd)
          (witnessFaces_subset_sideFaces hf)
      rcases witnessStepPinch_step_of_pieceEnd E hnb hr hlab hG1 hno hFa hFb hFi hFj hij hab
          hai hbi hai₁ haj₁ hbj₁ hcai hcaj hcbi hcbj K.firstArc hG₁ K.secondArc hG₂ with
        hstep | hpinch
      · exact hstep
      · exact hfwd n s t x y hr hcell hside hblock hcorner hpinch
  · exact Or.inr hbwd

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSkip_of_witnessStepPinch

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
