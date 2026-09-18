import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessPlanarAudit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessPlanarWalk
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-23: the corrected planar part

See the module docstring of `FourPieceWitnessPlanarAudit.lean`.  This module proves:
* the same witness under the connectivity hypotheses (A) and (B)
  (`FourPieceWitness.witnessFaces_enclosedFaceSetSucc_of_connected`);
* the planar statement implies the corrected one (`pocketFourPieceWitnessPlanarCorrected_of_planar`);
* the corrected residual of lane gl-p07-21c implies the corrected one
  (`pocketFourPieceWitnessPlanarCorrected_of_arcAuditResidual`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The witness has a successor outside walk without bridges** when its complement is
connected through edges (`hA`) and its boundary map is connected (`hB`). -/
theorem witnessFaces_enclosedFaceSetSucc_of_connected {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk) (hc : c ∈ sideFaces X.toCombMap K.walk)
    (hA : ∀ f, f ∉ witnessFaces a b K c →
      f ∈ PocketNoncrossing.faceClass X.toCombMap
        (boundaryKeep X.toCombMap (witnessFaces a b K c)) X.outerFace)
    (hB : (PocketOrbit.keepMap X.toCombMap (boundaryKeep X.toCombMap (witnessFaces a b K c))
      (boundaryKeep_alpha X.toCombMap (witnessFaces a b K c))).IsConnected) :
    ∃ outerWalk : List X.toCombMap.Dart,
      EnclosedFaceSetSucc X (witnessFaces a b K c) outerWalk ∧
        ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c :=
  exists_enclosedFaceSetSucc_of_connected (X := X) (F := witnessFaces a b K c)
    (fun h =>hout (witnessFaces_subset_sideFaces h)) ⟨c, mem_witnessFaces_self hc⟩ hA hB

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessFaces_enclosedFaceSetSucc_of_connected

end FourPieceWitness

/-- **The planar statement implies the corrected planar part.**  Branch 1 with `faces` the
witness, through `FourPieceWitness.dart_clause`. -/
theorem pocketFourPieceWitnessPlanarCorrected_of_planar
    (h : PocketFourPieceWitnessPlanarStatement.{u, w, v}) :
    PocketFourPieceWitnessPlanarCorrectedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb
  obtain ⟨outerWalk, E, hnb⟩ := h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁
    G₂ hG₂ hw hout hinner houter C hC hCf hCa hCb
  exact Or.inl ⟨FourPieceWitness.witnessFaces a b K C.face, outerWalk, E,
    FourPieceWitness.mem_witnessFaces_self hCf, FourPieceWitness.witnessFaces_subset_sideFaces,
    fun d hd => Or.inr (Or.inr (FourPieceWitness.dart_clause hw hCa hCb E hnb d hd))⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceWitnessPlanarCorrected_of_planar

/-- **The corrected residual of lane gl-p07-21c implies the corrected planar part.**  Branch 1
forgets the non-interleaving and arc clauses; branch 2 is the same. -/
theorem pocketFourPieceWitnessPlanarCorrected_of_arcAuditResidual
    (h : PocketFourPieceArcAuditResidualStatement.{u, w, v}) :
    PocketFourPieceWitnessPlanarCorrectedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb
  rcases h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
      houter C hC hCf hCa hCb with ⟨faces, outerWalk, E, hCF, hsub, hdart, _⟩ | hbr
  · exact Or.inl ⟨faces, outerWalk, E, hCF, hsub, hdart⟩
  · exact Or.inr hbr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketFourPieceWitnessPlanarCorrected_of_arcAuditResidual

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
