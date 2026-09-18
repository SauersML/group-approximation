import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoninterleaveStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockCurve
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-22: the pocket outer walk follows the pocket curve

Lane gl-p07-22.  The target is `PocketLabelFourBlockStatement` (`NoninterleaveStatement.lean`),
from Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This file states the residual, and
`FourBlockEndpoint.lean` proves the target from it.  Certifies no printed sentence on its own.

## The residual (`FourBlock.PocketCurveSublistStatement`)

Under the premise block of the target, some rotation `r` of `l = invDarts X outerWalk` satisfies
`r <+ w` or `r.reverse <+ w`, where
`w = invDarts G₁ ++ sideAWord a b G₁ G₂ ++ cellG2Word G₁ G₂ ++ sideBWord b G₁ G₂`
(`FourBlockCurve.lean`).  So `w` is the inverse pocket curve `Ḡ₁ · Ā · Ḡ₂ · B̄`, with every entry
kept only in the block of its priority class.

## Truth check

**The target is TRUE in every nondegenerate model checked**, and so is the residual.
* **Labels.**  Every entry of `l` is in `Ḡ₁` or `Ḡ₂`, or reverses a dart of `a.sideFrom j` or of
  `b.sideFrom i` (`pocketOrbitLabel`, `FourPieceOrder.lean`).  So each entry is in exactly one of
  the four words of `w`, the one of its priority class.
* **Reading.**  The fill of the pocket orbit of `C` is a union of sub-pockets joined at vertices.
  Its outer walk follows the pocket curve and skips the loops of sub-pockets it does not hold.
  Such a loop is a cyclic interval of `Γ`, so `l` is `Γ` with cyclic intervals deleted, read once
  around.  The walk is nodup.  Rotating `l` to its first position along `Γ` gives a sublist of `w`.
* **Orientation.**  `facePerm = σ ∘ α` matches the chaining convention of the walks, so the
  forward disjunct is expected.  The reverse disjunct is a hedge.
* **Models:** self-pinch of `Π_i`, lens between `Π_i` and `Π_j`, pinch of the two far sides, `a`
  and `b` sharing a pocket edge, and the wedge (vacuous).

## LOUD notes

1. **The target is stronger than what its consumer needs.**  `PocketLabelNoninterleavingStatement`
   holds for the cyclic word `G2 A G1 A`, which has no four-block form.  That consumer is off the
   live assembly route (`AssemblyResidual.lean`, "Not on this route").
2. **The premise block has no nondegeneracy hypothesis.**  `cellArcList_length_pos` needs
   `S.nondegenerate`, and it is not available here.  So the suggested route through edge-connected
   unions such as `Π_i ∪ b` cannot be instantiated when a contact arc is empty.  For the same
   reason a relator cell inside a region (for example `Π_i ∈ b.1`) cannot be excluded.
3. **Unverified case.**  Such a cell makes a far side run along `Π_i` or `Π_j`, so a dart is on
   two arcs of `Γ` at once.  If the walk passes it at its lower-priority position, the residual
   can fail there.  The target may still hold.  No counter-model was found, and none was ruled out.

## Why it is strictly smaller, and not a restatement

* **Not equivalent.**  The residual is strictly stronger as a conclusion.  It fixes the order
  inside each block, and it puts the `A` entries on `a.sideFrom j`.  The target asks for neither.
* **Strictly less proof content.**  The residual keeps only the planar step "the outer walk follows
  the pocket curve".  The rest is proved in `pocketLabelFourBlock_of_curveSublist`:
  - the priority bookkeeping (`mem_sideAWord`, `mem_cellG2Word`, `mem_sideBWord`);
  - the block split (`exists_blocks_of_sublist`);
  - the rotation that turns the reversed reading around (`exists_rotate_blocks_of_reverse_sublist`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse
  Surgery.MapCollapse.ExteriorComponent
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

/-- **Residual of lane gl-p07-22: the pocket outer walk follows the pocket curve.**  Some rotation
of `invDarts X outerWalk`, or its reverse, is a sublist of the priority-filtered inverse pocket
curve `Ḡ₁ · Ā · Ḡ₂ · B̄`.  See the module docstring for why it is true and smaller. -/
def PocketCurveSublistStatement : Prop :=
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
        ∃ n : ℕ,
          (invDarts X outerWalk).rotate n <+
              invDarts X G₁.darts ++ sideAWord a b G₁ G₂ ++ cellG2Word G₁ G₂ ++
                sideBWord b G₁ G₂ ∨
            ((invDarts X outerWalk).rotate n).reverse <+
              invDarts X G₁.darts ++ sideAWord a b G₁ G₂ ++ cellG2Word G₁ G₂ ++
                sideBWord b G₁ G₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.PocketCurveSublistStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock
