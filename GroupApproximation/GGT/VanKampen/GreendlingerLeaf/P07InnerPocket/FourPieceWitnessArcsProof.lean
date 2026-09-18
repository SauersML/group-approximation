import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessArcsStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-25: the corrected residual from the cut-down witness

Lane gl-p07-25.  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## `FourPieceWitness.arcsAudit_of_arcs`

The corrected arc statement `FourPieceWitness.ArcsAuditStatement` follows from the old
`PocketFourPieceWitnessArcsStatement`.
* 4a is the old clause with one hypothesis dropped.
* 4b is the old clause for the whole list, as the prefix of rotation `0`.

The old statement is false (model M2), so the corrected one is strictly weaker.

## `FourPieceWitness.arcAuditResidual_of_planar_noninterleave_arcsAudit`

This proves `PocketFourPieceArcAuditResidualStatement` (`FourPieceArcAuditStatement.lean`, lane
gl-p07-21c) through branch 1, with the witness `F = witnessFaces a b K C.face`.
1. `PocketFourPieceWitnessPlanarStatement` gives a bridge-free outside walk of `F` with
   `EnclosedFaceSetSucc`.
2. `C.face ∈ F` is `mem_witnessFaces_self`.
3. `F ⊆ sideFaces K.walk` is `witnessFaces_subset_sideFaces`.
4. Clause 2' is the third disjunct, from `dart_clause`.
5. The four noninterleaving facts come from `PocketFourPieceWitnessNoninterleaveStatement`.
6. Clauses 4a and 4b come from `ArcsAuditStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **The corrected arc statement follows from the old one.** -/
theorem arcsAudit_of_arcs (h : PocketFourPieceWitnessArcsStatement.{u, w, v}) :
    ArcsAuditStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  obtain ⟨harc₁, harc₂⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  refine ⟨fun m U V hm hU _ => harc₁ m U V hm hU, fun hall => ?_,
    fun m U V hm hU _ => harc₂ m U V hm hU, fun hall => ?_⟩
  · obtain ⟨A, hA⟩ := harc₁ 0 (invDarts X outerWalk) []
      (by rw [List.rotate_zero, List.append_nil]) hall
    exact ⟨0, A, by rw [List.rotate_zero, hA]⟩
  · obtain ⟨A, hA⟩ := harc₂ 0 (invDarts X outerWalk) []
      (by rw [List.rotate_zero, List.append_nil]) hall
    exact ⟨0, A, by rw [List.rotate_zero, hA]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcsAudit_of_arcs

/-- **The corrected residual from the cut-down witness.**  See the module docstring. -/
theorem arcAuditResidual_of_planar_noninterleave_arcsAudit
    (hplanar : PocketFourPieceWitnessPlanarStatement.{u, w, v})
    (hnon : PocketFourPieceWitnessNoninterleaveStatement.{u, w, v})
    (harcs : ArcsAuditStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  obtain ⟨outerWalk, E, hnb⟩ := hplanar D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
    G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hnon D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
    G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  obtain ⟨h4a₁, h4b₁, h4a₂, h4b₂⟩ := harcs D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
    G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  exact Or.inl ⟨witnessFaces a b K C.face, outerWalk, E, mem_witnessFaces_self hCf,
    witnessFaces_subset_sideFaces,
    fun d hd => Or.inr (Or.inr (dart_clause hw hCa hCb E hnb d hd)),
    hn1, hn2, hn3, hn4, h4a₁, h4b₁, h4a₂, h4b₂⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcAuditResidual_of_planar_noninterleave_arcsAudit

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
