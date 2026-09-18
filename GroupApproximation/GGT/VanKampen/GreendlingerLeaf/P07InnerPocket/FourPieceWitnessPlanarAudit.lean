import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-23: audit of the planar part for the cut-down witness

## LOUD: `PocketFourPieceWitnessPlanarStatement` is FALSE

The statement is in `FourPieceWitnessStatement.lean`.  Write `F = witnessFaces a b K C.face`.

*Model M8 (empty-arc island).*
* `Π_i` and `Π_j` touch at a vertex `w`.  `b` is an ordinary strip from `Π_i` to `Π_j`.  The pocket
  `P` is the disc bounded by `b.sideFrom j`, an arc of `Π_i` and an arc of `Π_j`, meeting at `w`.
* `a` has `source = i` and `target = some j`.  Both cell arcs are empty, `rightSide = []`, and
  `leftSide = ℓ` is a simple loop.  `a.1` is a disc of `G`-cells bounded by `ℓ`.  It lies inside
  `P` and shares no vertex with the pocket walk.
* Why `a` is allowed: `ContiguityGeometry` has no nondegeneracy field, `JoinsCells` reads only
  `source` and `target`, and a disc has a shelling.
* `K.secondSide = a.sideFrom i = []`, and `a.cellArcList i = a.cellArcList j = []`.  So
  `K.walk = b.sideFrom j ++ invDarts K.firstArc ++ invDarts K.secondArc` is a simple closed walk
  through `w`.
* The side `P` and the outside of the walk are discs, so `hinner` and `houter` hold.  `C` is a
  relator cell in `P \ a.1`.

The witness in M8:
* Every edge of `ℓ` is kept, so `keepClass C = P \ a.1`.
* `a.1` is off `block`, so it is cut.  So the open faces are `P \ a.1`, and `F = P \ a.1`, an
  annulus.

Why no outside walk exists:
* `EnclosedFaceSet.mem_iff` puts every boundary dart of `F` on the walk.  That includes the darts
  along `ℓ`, whose face is in `a.1`, and the darts along `K.walk`.
* At a vertex of `ℓ` the only edges of the walk are edges of `ℓ`.  So `turn_next` sends an
  `ℓ`-dart to an `ℓ`-dart.
* Running through the positions `i, i+1, …` visits every entry, so every entry is an `ℓ`-dart.
  This contradicts the darts along `K.walk`.

*Model M7* (lane gl-p07-21c, `FourPieceArcAuditStatement.lean`) has no witness for clauses 1 and 2.
The planar statement would give one: `pocketFourPieceWitnessPlanarCorrected_of_planar`
(`FourPieceWitnessPlanarCorrected.lean`) uses `FourPieceWitness.dart_clause`.  So M7 refutes it
as well, independently of M8.  M2 does not refute it: `F = {C}`, and the walk is the loop `λ`.

## The corrections

**(i) The same witness under connectivity hypotheses (proved).**
`FourPieceWitness.witnessFaces_enclosedFaceSetSucc_of_connected`
(`FourPieceWitnessPlanarCorrected.lean`) gives the conclusion of the planar statement for `F`
from:
* (A) the complement of `F` is connected through edges;
* (B) the map on the boundary edges of `F` is connected.
Both hypotheses fail in M8.

**(ii) The corrected planar part (`PocketFourPieceWitnessPlanarCorrectedStatement`).**  It has the
same premise block.  Its conclusion is one of two branches.
* Branch 1: an enclosed face set `faces ∋ C` with a successor walk, `faces ⊆ sideFaces K.walk`, and
  the per-dart clause 2'.
* Branch 2: an enclosed face set `faces ∋ C` whose rotated inverse walk is one cell arc of `i` or
  of `j`.

Why it is strictly weaker, and true:
* It follows from the planar statement (`pocketFourPieceWitnessPlanarCorrected_of_planar`), and the
  planar statement is false.  So it is strictly weaker.
* It follows from the corrected residual `PocketFourPieceArcAuditResidualStatement`
  (`pocketFourPieceWitnessPlanarCorrected_of_arcAuditResidual`).  The residual was checked on paper
  against M2, M5, M6 and M7.
* M8 does not refute it: take `faces = P`, which encloses the island.  Its reverse face along the
  walk lies in `P`, off `a.1` and `b.1`, on an edge of `K.walk`.

**Riskiest point:** the paper validity of M8, in particular that an empty-arc region candidate
is compatible with `hfirst`, `hsecond` and the noncrossing walk through the touching vertex `w`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The corrected planar part (lane gl-p07-23).**  See the module docstring. -/
def PocketFourPieceWitnessPlanarCorrectedStatement : Prop :=
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
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            faces ⊆ sideFaces X.toCombMap K.walk ∧
            ∀ d ∈ outerWalk,
              X.toCombMap.alpha d ∈ invDarts X G₁.darts ∨
              X.toCombMap.alpha d ∈ invDarts X G₂.darts ∨
              (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
                (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d)))) ∨
        (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            ((∃ A : CyclicArc (cellDarts X i),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
              (∃ A : CyclicArc (cellDarts X j),
                invDarts X (outerWalk.rotate n) = invDarts X A.darts)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceWitnessPlanarCorrectedStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
