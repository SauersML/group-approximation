import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInputProofStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21c: the corrected residual is weaker

`pocketFourPieceArcAuditResidual_of_inputProofResidual` proves the corrected residual
`PocketFourPieceArcAuditResidualStatement` (`FourPieceArcAuditStatement.lean`) from the original
`PocketFourPieceInputProofResidualStatement`.
* Branch 1 is used.
* Clause 2' comes from clause 2 by its third disjunct.
* Clause 4a is clause 4 with an extra hypothesis.
* Clause 4b is clause 4 for the whole list, as the prefix of the zeroth rotation.

The original residual is false (model M2, module docstring of `FourPieceArcAuditStatement.lean`).
So the corrected residual is strictly weaker.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The corrected residual follows from the original residual.** -/
theorem pocketFourPieceArcAuditResidual_of_inputProofResidual
    (h : PocketFourPieceInputProofResidualStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb
  obtain ⟨faces, outerWalk, E, hCF, hsub, hdart, hn1, hn2, hnb, hna, harc₁, harc₂⟩ :=
    h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter
      C hC hCf hCa hCb
  refine Or.inl ⟨faces, outerWalk, E, hCF, hsub, fun d hd => Or.inr (Or.inr (hdart d hd)),
    hn1, hn2, hnb, hna, fun m U V hm hU _ => harc₁ m U V hm hU, fun hall => ?_,
    fun m U V hm hU _ => harc₂ m U V hm hU, fun hall => ?_⟩
  · obtain ⟨A, hA⟩ := harc₁ 0 (invDarts X outerWalk) []
      (by rw [List.rotate_zero, List.append_nil]) hall
    exact ⟨0, A, by rw [List.rotate_zero, hA]⟩
  · obtain ⟨A, hA⟩ := harc₂ 0 (invDarts X outerWalk) []
      (by rw [List.rotate_zero, List.append_nil]) hall
    exact ⟨0, A, by rw [List.rotate_zero, hA]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceArcAuditResidual_of_inputProofResidual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
