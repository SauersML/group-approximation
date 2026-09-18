import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRouteStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcsAuditPinchProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditInside
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOffCell
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceNoPlanarStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-31: the sound route, proofs

See the module docstring of `SoundRouteStatement.lean`.  This module proves:
* `SoundRoute.arcAuditResidual_of_pinchCase`: the arc-audit residual from the residual, by the
  case split.  Case (i) uses the PROVED `FourPieceWitness.arcsAuditPinch`.
* `SoundRoute.pocketFourPieceInside_of_pinchCase` and
  **`SoundRoute.pocketFourPieceOff_of_pinchCase`**, through the proved `pocketFourPieceInside_of_arcAuditResidual` and
  `pocketFourPieceOff_of_inside`.
* `SoundRoute.pinchCase_of_arcAuditResidual_noninterleaveNondeg`: the residual is no stronger than
  the arc-audit residual together with lane 27's corrected noninterleave statement.
* `SoundRoute.noPlanarDegenerate_of_pinchCase`: the residual gives lane 28's
  `NoPlanarDegenerateStatement`.

No theorem here takes a statement marked FALSE as a hypothesis.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The arc-audit residual from the residual, by the case split.**  In case (i) branch 1 is built
with `faces = witnessFaces a b K C.face`.  Clause 3 comes from (read), and 4a/4b from the proved
`arcsAuditPinch`, whose pinch bound holds vacuously for pinch-free arcs.  Case (ii) is (rest). -/
theorem arcAuditResidual_of_pinchCase (h : PinchCaseStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  obtain ⟨hread, hrest⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  rcases Classical.em (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
      0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
      (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
      (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
      ∃ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
          ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
            FourPieceWitness.witnessFaces a b K C.face) with
    ⟨hai₁, haj₁, hbi₁, hbj₁, hpf₁, hpf₂, outerWalk, E, hnb⟩ | hcase
  · obtain ⟨hn1, hn2, hn3, hn4⟩ := hread hai₁ haj₁ hbi₁ hbj₁ outerWalk E hnb hpf₁ hpf₂
    obtain ⟨h4a₁, h4b₁, h4a₂, h4b₂⟩ := FourPieceWitness.arcsAuditPinch D eps X a b K hij hai hbi
      hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk
      E hnb
    exact Or.inl ⟨FourPieceWitness.witnessFaces a b K C.face, outerWalk, E,
      FourPieceWitness.mem_witnessFaces_self hCf, FourPieceWitness.witnessFaces_subset_sideFaces,
      fun d hd => Or.inr (Or.inr (FourPieceWitness.dart_clause hw hCa hCb E hnb d hd)),
      hn1, hn2, hn3, hn4, h4a₁ hpf₁, h4b₁ (fun d hd _ _ hnd _ => absurd (hpf₁ d hd) hnd),
      h4a₂ hpf₂, h4b₂ (fun d hd _ _ hnd _ => absurd (hpf₂ d hd) hnd)⟩
  · exact hrest hcase

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute.arcAuditResidual_of_pinchCase

/-- **`Inside` from the residual.** -/
theorem pocketFourPieceInside_of_pinchCase (h : PinchCaseStatement.{u, w, v}) :
    PocketFourPieceInsideStatement.{u, w, v} :=
  pocketFourPieceInside_of_arcAuditResidual (arcAuditResidual_of_pinchCase h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute.pocketFourPieceInside_of_pinchCase

/-- **Lane gl-p07-31 endpoint: `PocketFourPieceOffStatement` from the residual.**  Every other
input on the route is proved: `arcsAuditPinch`, `dart_clause`, `pocketFourPieceOffCell`
(through `pocketFourPieceOff_of_inside`) and `pocketFourPieceInside_of_arcAuditResidual`. -/
theorem pocketFourPieceOff_of_pinchCase (h : PinchCaseStatement.{u, w, v}) :
    PocketFourPieceOffStatement.{u, w, v} :=
  pocketFourPieceOff_of_inside (pocketFourPieceInside_of_pinchCase h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute.pocketFourPieceOff_of_pinchCase

/-- **The residual is no stronger than the arc-audit residual plus the corrected noninterleave
statement**: drop the pinch-free hypotheses from (read) and `¬ case (i)` from (rest). -/
theorem pinchCase_of_arcAuditResidual_noninterleaveNondeg
    (hres : PocketFourPieceArcAuditResidualStatement.{u, w, v})
    (hnon : FourPieceWitness.NoninterleaveNondegStatement.{u, w, v}) :
    PinchCaseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  exact ⟨fun hai₁ haj₁ hbi₁ hbj₁ outerWalk E hnb _ _ => hnon D eps X a b K hij hai hbi hab hai₁
      haj₁ hbi₁ hbj₁ hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa
      hCb outerWalk E hnb,
    fun _ => hres D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
      hinner houter C hC hCf hCa hCb⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute.pinchCase_of_arcAuditResidual_noninterleaveNondeg

/-- **The residual gives lane 28's no-walk residual**: "no witness walk" refutes case (i). -/
theorem noPlanarDegenerate_of_pinchCase (h : PinchCaseStatement.{u, w, v}) :
    FourPieceWitness.NoPlanarDegenerateStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb hno
  exact (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb).2 (fun hcase => hno hcase.2.2.2.2.2.2)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute.noPlanarDegenerate_of_pinchCase

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute
