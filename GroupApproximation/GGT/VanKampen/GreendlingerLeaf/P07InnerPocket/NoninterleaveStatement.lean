import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-17: the four-block reading of the pocket outer walk

Lane `gl-p07-17` (`lanes/carto-gl-p07.md`).  Target: `PocketLabelNoninterleavingStatement`
(`FourPieceOrder.lean`), from Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This file
states the residual; `NoninterleaveEndpoint.lean` proves the target from it.

## Notation

`l = invDarts X outerWalk`.  Four priority classes on darts `e`:
* `G1`: `e ∈ invDarts G₁`;
* `G2`: `e ∉ invDarts G₁` and `e ∈ invDarts G₂`;
* `B`: in neither, and `α e ∈ b.sideFrom i` (b far side);
* `A`: in neither, and `α e ∉ b.sideFrom i`.
The four target classes are `G1`, `G2`, `G1 ∪ B` and `G1 ∪ A`.

## The residual (`PocketLabelFourBlockStatement`)

Under the premise block of the target, some rotation of `l` reads `U₁ ++ U₂ ++ U₃ ++ U₄`, where:
* `U₁` lies in `G1` and `U₃` lies in `G2`;
* `U₂` and `U₄` both lie outside `G1` and `G2`;
* either `U₂ ⊆ B` and `U₄ ⊆ A`, or `U₂ ⊆ A` and `U₄ ⊆ B`.
The blocks may be empty.  So the outer walk reads the pocket curve
`Γ = Ḡ₂ · (b far side) · Ḡ₁ · (a far side)` blockwise, in one of its two orientations.

## Reduction (proved in `NoninterleaveEndpoint.lean`)

Each target class is `U₁`-inside, `U₃`-outside, and uniform on `U₂` and `U₄`, after rotating so
that the class's own block is `U₁` (`G2` uses the rotation `U₃ ++ U₄ ++ U₁ ++ U₂`).  So
`FourPiece.cyclicNoInterleave_of_four_blocks` gives all four facts.

## Truth check

**TRUE; no counter-model.**  Small models were checked, including self-pinched `Π_i` and hanging
cells.
* **Where the outer darts sit.**  Take `e ∈ l`.  It lies in `L`, and `α e` borders the outside
  component.  By the definition of `pocketKeep`, `α e` is on `Π_i` (then `e ∈ Ḡ₁`, since contact
  darts put `e` in `a` or `b`), or on `Π_j`, or on `∂a` or `∂b`.
* **The `A` class borders `a`.**  The Euler hypotheses separate `sideFaces K` from
  `sideOutside K`, so no pocket face is across a near side.
* **Pinches.**  A self-pinch of `Π_i` only splits `Ḡ₁` into `B̄₂ ++ B̄₁`, which is still one block.
  The sub-pocket is not in the class of `C`.
* **Absorbed cells.**  If `Π_i` or `Π_j` is absorbed, its block is empty (lane gl-p07-18's wedge).
* **Regions are edge-connected.**  `FaceSetBoundary` is a single inside-traversal cycle, so a
  vertex-pinched "flower" crossing of `a` and `b` does not exist.

**Why the blocks come in order** (Jordan, in the dual).  Contract the lake fill `D` of the class
of `C`, and the edge-connected regions `a` and `b`, to single vertices.  The rotation at `D` is the
cyclic order of `l`.
* **Step 1: the four target facts hold.**  For each target class `S`, the faces across `S` and
  the faces across `¬S` form two unions.  These are `Π_i` vs `a ∪ b ∪ Π_j`, `Π_j` vs the rest,
  `Π_i ∪ b` vs `Π_j ∪ a`, and `Π_i ∪ a` vs `Π_j ∪ b`.  Each union is edge-connected and outside
  `D`, and the two are face-disjoint, so their edges cannot interleave around `D`.
* **Step 2: list combinatorics.**  If `G1` and `G2` are both nonempty, step 1 forces each of the
  two gaps between them to be all `A` or all `B`.  If either of `G1`, `G2` is empty, step 1 gives
  at most three blocks, which already is the residual.
* **Step 3: the only extra case.**  Both gaps are `A`, say, with `B` empty, and `G1`, `G2` both
  nonempty.  The dual 2-cycle `D–a–D`, through one edge in each gap, separates the `Π_i`-edge from
  the `Π_j`-edge at `D`.  But `Π_i`, `b`, `Π_j` form a dual path that avoids `D` and `a`:
  * contact arcs are nonempty (`cellArcList_length_pos`);
  * `b` is edge-connected and disjoint from `a`;
  * `b` is not absorbed, because `Π_i` borders the outside component.
  This is a contradiction.  Swap `a` and `b` for the other case.

## Why it is strictly smaller, and not a restatement

* **Strictly stronger as a conclusion, so not equivalent.**  The cyclic word `G2 A G1 A` satisfies
  all four noninterleaving facts but has no four-block form.
* **Strictly less proof content.**  The residual keeps only the planar reading step.  The class
  bookkeeping and the cyclic-interval combinatorics are proved:
  * the priority classes;
  * the rotations;
  * `CyclicNoInterleave` from blocks (`NoninterleaveList.lean`).
* The residual is the form that downstream consumers (`PocketFourPieceOrderStatement`) actually
  use.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

/-- **Residual of lane gl-p07-17: the pocket outer walk reads four blocks.**  A rotation of
`invDarts X outerWalk` is `U₁ ++ U₂ ++ U₃ ++ U₄`, with `U₁ ⊆ Ḡ₁` and `U₃ ⊆ Ḡ₂` (off `Ḡ₁`).  The
blocks `U₂`, `U₄` are off both, and one of them reverses the b far side while the other does not.
See the module docstring for why it is true and smaller. -/
def PocketLabelFourBlockStatement : Prop :=
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
      ∀ L : List X.toCombMap.Dart,
        PocketNoncrossing.PocketOrbit X.toCombMap
          (PocketNoncrossing.pocketKeep X.toCombMap K.walk a.2.boundary.cycle b.2.boundary.cycle)
          C.face L →
      ∀ outerWalk : List X.toCombMap.Dart,
        EnclosedFaceSetSucc X (absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
          outerWalk →
        (∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
          X.toCombMap.faceOf d ∈ component X.toCombMap (sideFaces X.toCombMap L) X.outerFace) →
        ∃ (n : ℕ) (U₁ U₂ U₃ U₄ : List X.toCombMap.Dart),
          (invDarts X outerWalk).rotate n = U₁ ++ U₂ ++ U₃ ++ U₄ ∧
          (∀ e ∈ U₁, e ∈ invDarts X G₁.darts) ∧
          (∀ e ∈ U₃, e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts) ∧
          (∀ e ∈ U₂, e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) ∧
          (∀ e ∈ U₄, e ∉ invDarts X G₁.darts ∧ e ∉ invDarts X G₂.darts) ∧
          (((∀ e ∈ U₂, X.toCombMap.alpha e ∈ b.sideFrom i) ∧
              ∀ e ∈ U₄, X.toCombMap.alpha e ∉ b.sideFrom i) ∨
            ((∀ e ∈ U₂, X.toCombMap.alpha e ∉ b.sideFrom i) ∧
              ∀ e ∈ U₄, X.toCombMap.alpha e ∈ b.sideFrom i))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabelFourBlockStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
