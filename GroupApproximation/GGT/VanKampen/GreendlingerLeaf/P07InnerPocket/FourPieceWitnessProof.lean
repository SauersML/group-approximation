import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessRead
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21a: the residual from the cut-down witness

This module proves `PocketFourPieceInputProofResidualStatement`
(`FourPieceInputProofStatement.lean`, lane gl-p07-20b) from three isolated statements about the
witness `F = FourPieceWitness.witnessFaces a b K C.face` (`FourPieceWitnessDef.lean`).  The context
is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Proof route

Introduce the premise block, `C` and its hypotheses.
1. `PocketFourPieceWitnessPlanarStatement` (`FourPieceWitnessStatement.lean`) gives an outside walk
   `outerWalk` of `F` with `EnclosedFaceSetSucc` and no bridges.
2. `C.face ∈ F` is `FourPieceWitness.mem_witnessFaces_self`.
3. `F ⊆ sideFaces K.walk` is `FourPieceWitness.witnessFaces_subset_sideFaces` (clause 1).
4. The per-dart clause is `FourPieceWitness.dart_clause` (clause 2, `FourPieceWitnessDart.lean`).
5. The four noninterleaving facts come from `PocketFourPieceWitnessNoninterleaveStatement`
   (clause 3), and the two arc-run facts from `PocketFourPieceWitnessArcsStatement` (clause 4).
   Both are in `FourPieceWitnessRead.lean` and are applied to the walk of step 1.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

/-- **The reading residual from the cut-down witness.**  See the module docstring. -/
theorem inputProofResidual_of_witness_noninterleave_arcs
    (hplanar : PocketFourPieceWitnessPlanarStatement.{u, w, v})
    (hnon : PocketFourPieceWitnessNoninterleaveStatement.{u, w, v})
    (harcs : PocketFourPieceWitnessArcsStatement.{u, w, v}) :
    PocketFourPieceInputProofResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  obtain ⟨outerWalk, E, hnb⟩ := hplanar D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
    G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hnon D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
    G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  obtain ⟨harc₁, harc₂⟩ := harcs D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
    G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
  exact ⟨FourPieceWitness.witnessFaces a b K C.face, outerWalk, E,
    FourPieceWitness.mem_witnessFaces_self hCf, FourPieceWitness.witnessFaces_subset_sideFaces,
    FourPieceWitness.dart_clause hw hCa hCb E hnb, hn1, hn2, hn3, hn4, harc₁, harc₂⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.inputProofResidual_of_witness_noninterleave_arcs

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
