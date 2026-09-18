import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceNoPlanarStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessPlanarCorrected
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessArcsStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessNoninterleaveEndpoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-28: the corrected residual by a case split on the witness walk

See the module docstring of `FourPieceNoPlanarStatement.lean`.  This module proves:
* in case (ii), hypothesis (A) or (B) of lane gl-p07-23 fails
  (`FourPieceWitness.not_connected_of_not_exists_walk`);
* the residual is weaker than the target (`FourPieceWitness.noPlanarDegenerate_of_arcAuditResidual`)
  and than the planar statement (`FourPieceWitness.noPlanarDegenerate_of_planar`);
* the target from the residual, clause 3 and clause 4
  (`FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit`), and the same
  with the four-block reading (`FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_fourBlock_arcsAudit`).

None of these theorems takes `PocketFourPieceWitnessPlanarStatement` as a hypothesis, except
`noPlanarDegenerate_of_planar`, which only records that the residual is weaker.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **In case (ii) the connectivity hypotheses fail.**  If the witness has no bridge-free
successor outside walk, then (A) or (B) of `witnessFaces_enclosedFaceSetSucc_of_connected` fails. -/
theorem not_connected_of_not_exists_walk {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) (hc : c ∈ sideFaces X.toCombMap K.walk)
    (hno : ¬ ∃ outerWalk : List X.toCombMap.Dart,
      EnclosedFaceSetSucc X (witnessFaces a b K c) outerWalk ∧
        ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c) :
    ¬ ((∀ f, f ∉ witnessFaces a b K c →
        f ∈ PocketNoncrossing.faceClass X.toCombMap
          (boundaryKeep X.toCombMap (witnessFaces a b K c)) X.outerFace) ∧
      (PocketOrbit.keepMap X.toCombMap (boundaryKeep X.toCombMap (witnessFaces a b K c))
        (boundaryKeep_alpha X.toCombMap (witnessFaces a b K c))).IsConnected) := by
  rintro ⟨hA, hB⟩
  exact hno (witnessFaces_enclosedFaceSetSucc_of_connected hout hc hA hB)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.not_connected_of_not_exists_walk

end FourPieceWitness

namespace FourPieceWitness

/-- **The residual is weaker than the target**: drop the no-walk hypothesis. -/
theorem noPlanarDegenerate_of_arcAuditResidual
    (h : PocketFourPieceArcAuditResidualStatement.{u, w, v}) :
    NoPlanarDegenerateStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb _
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noPlanarDegenerate_of_arcAuditResidual

/-- **The residual is weaker than the (false) planar statement**: under the planar statement the
no-walk hypothesis is contradictory. -/
theorem noPlanarDegenerate_of_planar (h : PocketFourPieceWitnessPlanarStatement.{u, w, v}) :
    NoPlanarDegenerateStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb hno
  exact absurd (h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
    hinner houter C hC hCf hCa hCb) hno

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noPlanarDegenerate_of_planar

/-- **The corrected residual without the planar statement.**  Case (i), a witness walk exists:
branch 1 with `faces = witnessFaces a b K C.face`, from `hnon` and `harcs`.  Case (ii): `hdeg`. -/
theorem arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit
    (hdeg : NoPlanarDegenerateStatement.{u, w, v})
    (hnon : PocketFourPieceWitnessNoninterleaveStatement.{u, w, v})
    (harcs : ArcsAuditStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂
    hw hout hinner houter C hC hCf hCa hCb
  rcases Classical.em (∃ outerWalk : List X.toCombMap.Dart,
      EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk ∧
        ∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) with
    ⟨outerWalk, E, hnb⟩ | hno
  · obtain ⟨hn1, hn2, hn3, hn4⟩ := hnon D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond
      G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
    obtain ⟨h4a₁, h4b₁, h4a₂, h4b₂⟩ := harcs D eps X a b K hij hai hbi hab hlabel hW hfirst
      hsecond G₁ hG₁ G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb outerWalk E hnb
    exact Or.inl ⟨witnessFaces a b K C.face, outerWalk, E, mem_witnessFaces_self hCf,
      witnessFaces_subset_sideFaces,
      fun d hd => Or.inr (Or.inr (dart_clause hw hCa hCb E hnb d hd)),
      hn1, hn2, hn3, hn4, h4a₁, h4b₁, h4a₂, h4b₂⟩
  · exact hdeg D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout
      hinner houter C hC hCf hCa hCb hno

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit

/-- **The same with the four-block reading** (lane gl-p07-27's `FourBlockStatement`) in place of
clause 3, through `noninterleave_of_fourBlock`. -/
theorem arcAuditResidual_of_noPlanarDegenerate_fourBlock_arcsAudit
    (hdeg : NoPlanarDegenerateStatement.{u, w, v})
    (hblock : FourBlockStatement.{u, w, v})
    (harcs : ArcsAuditStatement.{u, w, v}) :
    PocketFourPieceArcAuditResidualStatement.{u, w, v} :=
  arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit hdeg
    (noninterleave_of_fourBlock hblock) harcs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_fourBlock_arcsAudit

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
