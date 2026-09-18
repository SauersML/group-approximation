import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInputProofStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21a: the planar part for the cut-down witness

This module isolates the planar part of `PocketFourPieceInputProofResidualStatement`
(`FourPieceInputProofStatement.lean`) for the witness `F = FourPieceWitness.witnessFaces a b K C.face`
(`FourPieceWitnessDef.lean`).  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma
9.7(b).

## The statement

`PocketFourPieceWitnessPlanarStatement`: under the premise block of the residual, `F` has an
outside walk that turns to its successor (`EnclosedFaceSetSucc`) and has no bridges.  Every walk
dart `d` has `faceOf (α d) ∈ F`.

## Why it is strictly smaller

The residual asks for an enclosed face set with four more groups of clauses.  Clauses 1 and 2 are
proved for `F` and any bridge-free outside walk (`FourPieceWitness.witnessFaces_subset_sideFaces`,
`FourPieceWitness.dart_clause`).  Clauses 3 and 4 are the two statements of
`FourPieceWitnessRead.lean`.  This statement keeps the whole premise block and asserts only the
walk, with no reading clause.

## Why it is true

Write `P` for the blocking set and `T` for the open faces.
* **`o ∉ F`**, since `F ⊆ sideFaces K.walk` and `o ∉ sideFaces K.walk`.  `F` is nonempty since
  `C.face ∈ F`.
* **`F` is connected through vertices** by construction.
* **The complement of `F` is connected through edges.**
  * `sideOutside K.walk` is connected through edges.  Its reclosing keeps the Euler
    characteristic (`houter`), so it is one disc-like region.
  * A cut piece holds a face of `a` or `b`.  The region is connected through edges (its
    `FaceShelling`) and touches `Π_i ∈ sideOutside K.walk` along its cell arc.  So a path in the
    region runs, off `P`, to an edge of `sideOutside K.walk`.
  * An open face `g ∉ F` has no edge to `F`, since an edge is a touch.  It has no edge to a cut
    piece either: both faces are off `P`, so the edge would be crossed and `g` would be cut.  So
    it reaches `sideOutside K.walk` through open faces off `F`.
* **One orbit.**  On the sphere, the boundary orbits of `F` match the boundaries between the
  corner-separated complement pieces and the vertex-connected pieces of `F`.  These form a tree.
  With one piece on each side there is one orbit.
* **No bridges.**  A walk dart whose two faces are off `F` would join two corners of `F` through
  a complement face.  Every face that touches `F` at a vertex and is open is already in `F`.
  Spurs of cut or outside faces are skipped by the turn (`turn_mem` asks only about edges of the
  walk).

**Models.**
* *Self-pinch:* `F = cls C ∪ P' ∪ lakes`, and the walk follows the loop.
* *Wedge* (`FourPieceOffSplit.lean`): `sideOutside = {o, Π_i, Π_j}` has no internal edge, so
  `houter` fails and the model is vacuous.
* *`a = b = ∅`:* `F = sideFaces K.walk`.
* *Lens, and a pinched hole of `a` on a near side:* the strip is cut and its hole reaches `o`.

**Riskiest point:** the edge-connectivity of `sideOutside K.walk` read off `houter`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The planar part for the cut-down witness.**  See the module docstring. -/
def PocketFourPieceWitnessPlanarStatement : Prop :=
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
        ∃ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
            ∀ d ∈ outerWalk,
              X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ FourPieceWitness.witnessFaces a b K C.face

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceWitnessPlanarStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
