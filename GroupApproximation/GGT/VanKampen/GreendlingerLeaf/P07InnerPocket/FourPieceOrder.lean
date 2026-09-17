import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceListOrder
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossingWalk
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLakeFill
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBoundCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: four-piece cyclic order of the pocket outer walk

Lane `gl-p07-10` (`lanes/carto-gl-p07.md`).  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

## Statement (`PocketFourPieceOrderStatement`)

Assume the hypothesis block of the lane.  `L` is the pocket face orbit (lane 05's `PocketOrbit`)
and `outerWalk` is a lake-filled outer walk with lane 06's membership clause.  Then some rotation of
the outer walk satisfies `invDarts X (outerWalk.rotate n) = R₁ ++ U₁ ++ R₂ ++ U₂`, where:
* `U₁` lies in `invDarts G₁` and `U₂` lies in `invDarts G₂`;
* either each `Rₖ` reverses only one far side (`a.sideFrom j` or `b.sideFrom i`), or `R₁ ++ R₂`
  reverses far-side darts and `U₁ = []` or `U₂ = []`.

Truth check: TRUE; no counter-model.  Pairwise non-interleaving of the labels is not enough (the
cyclic word `1 a 1 b` is pairwise fine but has no four-piece form).  The residual below uses four
classes, which rule this word out.

## Mathematical proof

1. **Labels** (lane 08, `pocketOrbitLabel`, proved).  Every dart `e ∈ L` is in `invDarts G₁` or in
   `invDarts G₂`, or `α e` is in `a.sideFrom j` or in `b.sideFrom i`.  The darts of
   `invDarts outerWalk` are `α d` with `d ∈ outerWalk`, so they lie in `L` by the membership clause.
2. **Jordan-type order** (the residual).  The pocket side of `K.walk`, minus the regions `a` and
   `b`, is bounded by a closed curve `Γ`.  Read cyclically, `Γ` is the reversed arcs
   `Ḡ₂ · (b far side) · Ḡ₁ · (a far side)`, as lane 08's case analysis of retained edges shows.
   Filling the lakes of the class of `C` leaves a closed disc inside `Γ`.  Its outer walk crosses
   no edge of `Γ` transversally, so its darts on `Γ` are read in the cyclic order of `Γ`: a cyclic
   subsequence.  In `Γ`, each of the following four classes is a single cyclic block, so none of
   them interleaves (`A, ¬A, A, ¬A`) in any rotation of `invDarts outerWalk`:
   * `P1 = invDarts G₁`;
   * `¬P1 ∧ P2` (the block `Ḡ₂`);
   * `P1 ∨ (¬P2 ∧ Pb)` (the blocks `Ḡ₁`, b far side);
   * `P1 ∨ (¬P2 ∧ ¬Pb)` (the blocks `Ḡ₁`, a far side).
   The priorities `P1 > P2 > Pb` make these classes well defined on every dart.
3. **List combinatorics** (`FourPiece.exists_fourPiece`, proved).  Rotate `P1` to the front:
   `U ++ V`.
   * If `U = []`, rotate the `P2` block to the back.  The rest is all far side, and `U₁ = []`.
   * Otherwise, split `V` greedily as `X · W · Y` with `X, Y` not `P2` and `W` in `P2`.
     A second `P2` block would interleave `¬P1 ∧ P2`.  Take `U₁ = U`, `U₂ = W`, `R₂ = X`,
     `R₁ = Y`.  If `X` contained an `a`-dart and a `b`-dart, the heads of `U`, the two darts and
     `W` would interleave class 3 or class 4; likewise for `Y` (`FourPiece.mono_or`).
4. **Rotation** (`SideBound.exists_rotate_invDarts`, proved).  A rotation of `invDarts outerWalk`
   is `invDarts` of a rotation of `outerWalk`.

## Residual gap (`PocketLabelNoninterleavingStatement`)

The residual is exactly step 2: four `FourPiece.CyclicNoInterleave` facts on
`invDarts X outerWalk`.  It is TRUE by the Jordan-type argument of step 2.  It has strictly less
proof content than the target: steps 1, 3 and 4 are proved here, and the reduction
`pocketFourPieceOrder_of_noninterleaving` is proved.  It is not a restatement of the target: it
says nothing about labels, blocks, or rotations of `outerWalk`, which the proved steps supply.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

/-- **Residual: the four label classes do not interleave along the pocket outer walk.**
The step-2 input of the lane; see the module docstring for why it is true and smaller. -/
def PocketLabelNoninterleavingStatement : Prop :=
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
        FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts) (invDarts X outerWalk) ∧
        FourPiece.CyclicNoInterleave
          (fun e => e ∉ invDarts X G₁.darts ∧ e ∈ invDarts X G₂.darts) (invDarts X outerWalk) ∧
        FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
          (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∈ b.sideFrom i))
          (invDarts X outerWalk) ∧
        FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts ∨
          (e ∉ invDarts X G₂.darts ∧ X.toCombMap.alpha e ∉ b.sideFrom i))
          (invDarts X outerWalk)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabelNoninterleavingStatement
