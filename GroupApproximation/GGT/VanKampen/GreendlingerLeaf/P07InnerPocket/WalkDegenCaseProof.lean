import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenCaseStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenCaseBase
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenStepProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-39b: the walk-degenerate step residual from the case split

* `PinchCase.walkDegenCase_step`: `WalkDegenCaseStatement` implies lane gl-p07-37c's
  `WalkDegenStepStatement`.  Base comes from `walkDegenCase_witness_basic` when N holds and from
  the residual when N fails.  Lane 38's `absorbFaceSet_iterate` then runs with Improve, and the
  exposed dart comes from `absorbFaceSet_exposed_of_basic`.
* `PinchCase.walkDegenCase_of_step` and `PinchCase.walkDegenCase_iff_step`: the converse, and the
  equivalence (LOUD, see `WalkDegenCaseStatement.lean`).
* `PinchCase.walkDegenCase_walkDegen` and `PinchCase.walkDegenCase_pocketFourPieceOff`: the
  consumers.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane gl-p07-39b: the target from the case split and the absorption iteration.** -/
theorem walkDegenCase_step (h : WalkDegenCaseStatement.{u, w, v}) :
    WalkDegenStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hnd hbad
  obtain ⟨hbase, himp⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hnd hbad
  have hbase' : (∃ (F : Finset X.toCombMap.Face) (ow : List X.toCombMap.Dart),
      FourPieceWitness.AbsorbFaceSetBasic a b K G₁ G₂ C.face F ow) ∨
      FourPieceWitness.AbsorbFaceSetBranchTwo i j C.face := by
    by_cases hN : WalkDegenCaseNoninterleave b G₁ G₂ outerWalk
    · exact Or.inl ⟨_, _, walkDegenCase_witness_basic hw hCf hCa hCb E hnb hN⟩
    · exact hbase hN
  rcases FourPieceWitness.absorbFaceSet_iterate (β := X.toCombMap.Face)
      (γ := List X.toCombMap.Dart)
      (B := fun F ow => FourPieceWitness.AbsorbFaceSetBasic a b K G₁ G₂ C.face F ow)
      (S := fun _ ow => FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ ow)
      (R := FourPieceWitness.AbsorbFaceSetBranchTwo i j C.face) hbase'
      (fun F ow hB hS => himp F ow hB hS
        (FourPieceWitness.absorbFaceSet_exposed_of_basic K hG₁ hG₂ hB hS)) with
    ⟨F, ow, ⟨E', hc, hsub, hd, h1, h2, h3, h4⟩, s1, s2, s3, s4⟩ | hR
  · exact Or.inl ⟨F, ow, E', hc, hsub, hd, h1, h2, h3, h4, s1, s2, s3, s4⟩
  · exact Or.inr hR

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegenCase_step

/-- **The converse.**  A good pair of the target serves Base and every Improve step, and branch 2
serves both parts. -/
theorem walkDegenCase_of_step (h : WalkDegenStepStatement.{u, w, v}) :
    WalkDegenCaseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb hnd hbad
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb outerWalk E hnb hnd hbad with
    ⟨F, ow, E', hc, hsub, hd, h1, h2, h3, h4, s1, s2, s3, s4⟩ | hR
  · exact ⟨fun _ => Or.inl ⟨F, ow, E', hc, hsub, hd, h1, h2, h3, h4⟩,
      fun _ _ _ _ _ => Or.inl ⟨F, ow, ⟨E', hc, hsub, hd, h1, h2, h3, h4⟩,
        Or.inr ⟨s1, s2, s3, s4⟩⟩⟩
  · exact ⟨fun _ => Or.inr hR, fun _ _ _ _ _ => Or.inr hR⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegenCase_of_step

/-- **The case split and the target are equivalent** (LOUD: not weaker as a `Prop`). -/
theorem walkDegenCase_iff_step :
    WalkDegenCaseStatement.{u, w, v} ↔ WalkDegenStepStatement.{u, w, v} :=
  ⟨walkDegenCase_step, walkDegenCase_of_step⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegenCase_iff_step

/-- **Lane 34's walk-degenerate residual from the case split.** -/
theorem walkDegenCase_walkDegen (h : WalkDegenCaseStatement.{u, w, v}) :
    WalkDegenStatement.{u, w, v} :=
  walkDegen_of_step (walkDegenCase_step h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegenCase_walkDegen

/-- **`PocketFourPieceOffStatement` through the absorption residuals**: gl-p07-32's
`WitnessCurveSublistNondegStatement`, gl-p07-38's `AbsorbFaceSetStatement` for the no-walk case,
and this lane's `WalkDegenCaseStatement` for the walk-degenerate case. -/
theorem walkDegenCase_pocketFourPieceOff
    (hcurve : FourPieceWitness.WitnessCurveSublistNondegStatement.{u, w, v})
    (habs : FourPieceWitness.AbsorbFaceSetStatement.{u, w, v})
    (hcase : WalkDegenCaseStatement.{u, w, v}) : PocketFourPieceOffStatement.{u, w, v} :=
  walkDegen_pocketFourPieceOff_of_step hcurve
    (FourPieceWitness.noPlanarDegenStep_of_absorbFaceSet habs) (walkDegenCase_step hcase)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.walkDegenCase_pocketFourPieceOff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
