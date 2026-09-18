import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessPlanarCorrected
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-43: the planar part for the witness, closed where it is true

The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The lane target is
`PocketFourPieceWitnessPlanarStatement` (`FourPieceWitnessStatement.lean:67`).

## LOUD: the target is FALSE as stated (confirmed, not new)

Lane gl-p07-23 (`FourPieceWitnessPlanarAudit.lean`) refutes it with model M8, the empty-arc
island, and independently with M7.  Re-check of M8 on paper, with `F = witnessFaces a b K C.face`:
* `a` has empty cell arcs, `rightSide = []` and `leftSide = ℓ` a simple loop around a disc
  `a.1` inside the pocket `P`, sharing no vertex with `K.walk`.
* Every edge of `ℓ` is kept, and `a.1` is off the blocking set, so `F = P \ a.1`, an annulus.
* `EnclosedFaceSet.mem_iff` forces both the `ℓ`-darts and the `K.walk`-darts onto one walk, while
  `turn_next` keeps an `ℓ`-dart walk on `ℓ` (no walk edge meets `ℓ` elsewhere).  Contradiction.
No hypothesis of the premise block excludes M8 (`ContiguityGeometry` has no nondegeneracy field).
So the target cannot be proved, and it is not reduced here.

## What this module proves outright

The planar statement restricted to the case where the two connectivity hypotheses of lane 23
hold, for the witness itself:
* **(A)** every face off `F` is in the edge class of the outer face for `boundaryKeep F`;
* **(B)** the map on the boundary edges of `F` is connected.

This is `WitnessPlanarCloseConnectedStatement`, proved by `witnessPlanarCloseConnected`.

**Strictly weaker than the target, and true.**
* It is the target with the two extra hypotheses (A), (B), so the target implies it.
* The target is false (M8), and this statement is proved, so the two are not equivalent.
* In M8 both (A) and (B) fail: `a.1` is off `F` but separated from `o` by the kept loop `ℓ`, and
  the boundary edges of `F` are `ℓ` and `K.walk`, two components.

**The complementary case** (no witness walk) is exactly lane 28's case (ii), where
`FourPieceWitness.not_connected_of_not_exists_walk` shows that (A) ∧ (B) fails.  That case is
handled on the sound route by `FourPieceWitness.NoPlanarDegenerateStatement` and its step forms
(sibling lanes).  See `WitnessPlanarCloseRoute.lean` for the rerouting of the corrected planar
part `PocketFourPieceWitnessPlanarCorrectedStatement` to those live gaps.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The planar part for the witness under the connectivity hypotheses (lane gl-p07-43).**  The
premise block of `PocketFourPieceWitnessPlanarStatement`, plus (A) and (B) for
`witnessFaces a b K C.face`; the conclusion is that of the planar statement.  See the module
docstring for why it is strictly weaker than the (false) planar statement. -/
def WitnessPlanarCloseConnectedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    ∀ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i →
    ∀ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
      (∀ f, f ∉ FourPieceWitness.witnessFaces a b K C.face →
        f ∈ PocketNoncrossing.faceClass X.toCombMap
          (FourPieceWitness.boundaryKeep X.toCombMap
            (FourPieceWitness.witnessFaces a b K C.face)) X.outerFace) →
      (PocketOrbit.keepMap X.toCombMap
        (FourPieceWitness.boundaryKeep X.toCombMap (FourPieceWitness.witnessFaces a b K C.face))
        (FourPieceWitness.boundaryKeep_alpha X.toCombMap
          (FourPieceWitness.witnessFaces a b K C.face))).IsConnected →
        ∃ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
            ∀ d ∈ outerWalk,
              X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ FourPieceWitness.witnessFaces a b K C.face

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessPlanarCloseConnectedStatement

/-- **The planar part under (A) and (B), proved outright**, from lane 23's
`FourPieceWitness.witnessFaces_enclosedFaceSetSucc_of_connected`. -/
theorem witnessPlanarCloseConnected : WitnessPlanarCloseConnectedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K _ _ _ _ _ _ _ _ _ _ _ _ _ hout _ _ C _ hCf _ _ hA hB
  exact FourPieceWitness.witnessFaces_enclosedFaceSetSucc_of_connected hout hCf hA hB

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessPlanarCloseConnected

/-- **The (false) planar statement implies the connected case**: drop (A) and (B).  Recorded
only to certify that `WitnessPlanarCloseConnectedStatement` is no stronger than the target. -/
theorem witnessPlanarCloseConnected_of_planar
    (h : PocketFourPieceWitnessPlanarStatement.{u, w, v}) :
    WitnessPlanarCloseConnectedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw
    hout hinner houter C hC hCf hCa hCb _ _
  exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond G₁ hG₁ G₂ hG₂ hw hout hinner
    houter C hC hCf hCa hCb

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessPlanarCloseConnected_of_planar

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
