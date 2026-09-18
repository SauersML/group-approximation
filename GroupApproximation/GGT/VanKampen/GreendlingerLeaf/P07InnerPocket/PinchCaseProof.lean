import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseGlue
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseResidualStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCaseWalkStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRouteProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceNoPlanarStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoPlanarDegenStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockNondegStepProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-34: proofs for the good-walk cut of clause (rest)

* `PinchCase.rest_of_residual`: (rest) from `ResidualStatement`; the good-walk case is proved.
* `PinchCase.residual_of_rest`: the converse (LOUD: the two statements are equivalent).
* `PinchCase.residual_of_noPlanarDegenerate_walkDegen`: the residual from lane 28's no-walk
  residual and `WalkDegenStatement`.
* `PinchCase.walkDegen_of_rest`: `WalkDegenStatement` is no stronger than (rest).
* End-to-end consumers of `PocketFourPieceOffStatement`, including one through the gaps of the
  sibling lanes gl-p07-32 (`WitnessCurveSublistNondegStatement`) and gl-p07-33
  (`NoPlanarDegenStepStatement`).

None of these routes goes through the FALSE `InputProofResidual`, `WitnessPlanar`,
`WitnessNoninterleave`, `FourBlock` or `ArcsAudit` statements.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Clause (rest) from the residual.**  A good witness walk gives branch 1 with
`faces = witnessFaces a b K C.face`; no good walk is the residual. -/
theorem rest_of_residual (h : ResidualStatement.{u, w, v}) : RestStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase
  refine Classical.byContradiction fun hcon => hcon (h D eps X a b K hij hai hbi hab hlabel hW
    hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb hcase ?_)
  rintro ⟨outerWalk, E, hnb, hn1, hn2, hn3, hn4, hs₁, hu₁, hs₂, hu₂⟩
  refine hcon (Or.inl ⟨FourPieceWitness.witnessFaces a b K C.face, outerWalk, E,
    FourPieceWitness.mem_witnessFaces_self hCf, FourPieceWitness.witnessFaces_subset_sideFaces,
    fun d hd => Or.inr (Or.inr (FourPieceWitness.dart_clause hw hCa hCb E hnb d hd)),
    hn1, hn2, hn3, hn4, ?_, ?_, ?_, ?_⟩)
  · intro m U V hm hU hV
    exact ArcClose.arc_of_block E i G₁ (hs₁ (ArcClose.exists_not_mem_of_block G₁ hm hV)) hm hU
  · intro hall
    exact ArcClose.arc_of_all E i G₁ (ArcClose.all_mem_of_invDarts G₁ hall)
      (hu₁ (ArcClose.all_mem_of_invDarts G₁ hall))
  · intro m U V hm hU hV
    exact ArcClose.arc_of_block E j G₂ (hs₂ (ArcClose.exists_not_mem_of_block G₂ hm hV)) hm hU
  · intro hall
    exact ArcClose.arc_of_all E j G₂ (ArcClose.all_mem_of_invDarts G₂ hall)
      (hu₂ (ArcClose.all_mem_of_invDarts G₂ hall))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.rest_of_residual

/-- **LOUD: the residual from clause (rest)**, by dropping the no-good-walk hypothesis.  So the
residual is logically equivalent to (rest); it is smaller only in proof content. -/
theorem residual_of_rest (h : RestStatement.{u, w, v}) : ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase _
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb hcase

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.residual_of_rest

/-- **The residual from lane 28's no-walk residual and the walk-degenerate residual.**  Split on
whether `witnessFaces a b K C.face` has a witness walk. -/
theorem residual_of_noPlanarDegenerate_walkDegen
    (hdeg : FourPieceWitness.NoPlanarDegenerateStatement.{u, w, v})
    (hwalk : WalkDegenStatement.{u, w, v}) : ResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb hcase hgood
  rcases Classical.em (∃ outerWalk : List X.toCombMap.Dart,
      EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
        ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
          FourPieceWitness.witnessFaces a b K C.face) with
    ⟨outerWalk, E, hnb⟩ | hno
  · refine hwalk D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
      hinner houter C hC hCf hCa hCb outerWalk E hnb ?_ ?_
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact hcase ⟨h1, h2, h3, h4, h5, h6, outerWalk, E, hnb⟩
    · rintro ⟨hn1, hn2, hn3, hn4, hs₁, hu₁, hs₂, hu₂⟩
      exact hgood ⟨outerWalk, E, hnb, hn1, hn2, hn3, hn4, hs₁, hu₁, hs₂, hu₂⟩
  · exact hdeg D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
      hinner houter C hC hCf hCa hCb hno

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.residual_of_noPlanarDegenerate_walkDegen

/-- **The walk-degenerate residual is no stronger than clause (rest)**: a witness walk with
`¬ (arcs nonempty ∧ pinch-free)` refutes case (i). -/
theorem walkDegen_of_rest (h : RestStatement.{u, w, v}) : WalkDegenStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb _ _ _ hnd _
  refine h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb ?_
  rintro ⟨h1, h2, h3, h4, h5, h6, _⟩
  exact hnd ⟨h1, h2, h3, h4, h5, h6⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegen_of_rest

/-- **`PocketFourPieceOffStatement` from clause (read) and the residual.** -/
theorem pocketFourPieceOff_of_read_residual (hread : ReadStatement.{u, w, v})
    (hres : ResidualStatement.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  SoundRoute.pocketFourPieceOff_of_pinchCase (pinchCase_of_read_rest hread (rest_of_residual hres))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.pocketFourPieceOff_of_read_residual

/-- **`PocketFourPieceOffStatement` from clause (read), the no-walk residual and the
walk-degenerate residual.** -/
theorem pocketFourPieceOff_of_read_noPlanarDegenerate_walkDegen (hread : ReadStatement.{u, w, v})
    (hdeg : FourPieceWitness.NoPlanarDegenerateStatement.{u, w, v})
    (hwalk : WalkDegenStatement.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  pocketFourPieceOff_of_read_residual hread (residual_of_noPlanarDegenerate_walkDegen hdeg hwalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.pocketFourPieceOff_of_read_noPlanarDegenerate_walkDegen

/-- **`PocketFourPieceOffStatement` through the gaps of the sibling lanes**: gl-p07-32's
`WitnessCurveSublistNondegStatement` for (read), gl-p07-33's `NoPlanarDegenStepStatement` for
the no-walk case, and this lane's `WalkDegenStatement`. -/
theorem pocketFourPieceOff_of_curveSublist_noPlanarDegenStep_walkDegen
    (hcurve : FourPieceWitness.WitnessCurveSublistNondegStatement.{u, w, v})
    (hstep : FourPieceWitness.NoPlanarDegenStepStatement.{u, w, v})
    (hwalk : WalkDegenStatement.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  pocketFourPieceOff_of_read_noPlanarDegenerate_walkDegen
    (read_of_noninterleaveNondeg (FourPieceWitness.noninterleaveNondeg_of_curveSublist hcurve))
    (FourPieceWitness.noPlanarDegenerate_of_step hstep) hwalk

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.pocketFourPieceOff_of_curveSublist_noPlanarDegenStep_walkDegen

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
