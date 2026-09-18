import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceInputProofStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-21a: the reading clauses for the cut-down witness

Clauses 3 and 4 of `PocketFourPieceInputProofResidualStatement` (`FourPieceInputProofStatement.lean`)
for `F = FourPieceWitness.witnessFaces a b K C.face` (`FourPieceWitnessDef.lean`).  The context is
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Both statements keep the whole premise
block.  They quantify over every bridge-free outside walk of `F` that turns to its successor.  Such
a walk is one orbit of the restricted face permutation, so it is unique up to rotation.  Both
conclusions are invariant under rotation (`CyclicNoInterleave` is cyclic, and clause 4 already
ranges over all rotations).  So the universal form is equivalent to the existential one.

## `PocketFourPieceWitnessNoninterleaveStatement` (clause 3)

These are the four noninterleaving facts of `PocketLabelNoninterleavingStatement`
(`FourPieceOrder.lean`, lane gl-p07-17), for this walk instead of the lake fill of `L_C`.
* **Why true:** gl-p07-17's planarity argument.  `F` is connected through vertices and its
  complement is connected through edges (`FourPieceWitnessStatement.lean`).  So the reversed
  outside walk reads the boundary of one disc-like region inside `sideFaces K.walk`.  A reading
  `x … y … x … y` with `x, y` on one arc and the other entries on a different piece gives two
  crossing chords inside the region.  The chords run through `Π_i` and through a far side, which
  lie off `F`, a contradiction.
* **Models:**
  * self-pinch: the loop is read in order;
  * wedge: vacuous;
  * `a = b = ∅`: the region is the pocket itself.

## `PocketFourPieceWitnessArcsStatement` (clause 4)

Every block of the reversed walk inside `invDarts G₁` is `invDarts A` for a cell arc `A` of `Π_i`.
The same holds for `G₂` and `Π_j`.
* **Why true:** `F` holds every sub-pocket at a vertex of its boundary on `G₁`.  A sub-pocket is
  open (it is off `P` and joined to no strip), and it touches `F`.  So at such a vertex the walk
  turns into the loop and consecutive walk darts on `Π_i` are `facePerm`-consecutive.
* **Models:**
  * self-pinch: `P' ⊆ F`, and the block is the whole of `G₁` read backwards;
  * a strip corner at a pinch vertex with `C` away from it: the walk leaves `Π_i` before the
    vertex, and the blocks stay contiguous.

**Riskiest point:** clause 4 at a pinch vertex shared by `C`, a far side and a loop of `G₁`.  Lane
gl-p07-21c audits clause 4.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Clause 3 for the cut-down witness**: the four noninterleaving facts.  See the module
docstring. -/
def PocketFourPieceWitnessNoninterleaveStatement : Prop :=
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
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ FourPieceWitness.witnessFaces a b K C.face) →
        FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
            (invDarts X outerWalk) ∧
          FourPiece.CyclicNoInterleave
            (fun e => e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts)
            (invDarts X outerWalk) ∧
          FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
            (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i))
            (invDarts X outerWalk) ∧
          FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
            (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i))
            (invDarts X outerWalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceWitnessNoninterleaveStatement

/-- **Clause 4 for the cut-down witness**: blocks of gap darts are cell arcs.  See the module
docstring. -/
def PocketFourPieceWitnessArcsStatement : Prop :=
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
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ FourPieceWitness.witnessFaces a b K C.face) →
        (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate m = U ++ V →
          (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
          ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
        (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate m = U ++ V →
          (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
          ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceWitnessArcsStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
