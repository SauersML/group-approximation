import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceOffSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceListOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-20b: the reading part, reduced to one residual

The target is `PocketFourPieceInsideStatement` (`FourPieceOffSplit.lean`).  It is the reading part
of `PocketFourPieceOffStatement`, from Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
Lane gl-p07-20a proves `pocketFourPieceOff_of_inside`.

## LOUD: the reading cannot come from the pocket orbit `L_C` alone

`PocketLabelNoninterleavingStatement` (`FourPieceOrder.lean`, lane gl-p07-17) is about the lake
fill of the pocket orbit `L_C` of `C`.  That witness does **not** carry the reading.

*Self-pinch model.*  `G₁` passes a vertex `v` twice.  The loop of `G₁` between the two visits
encloses a sub-pocket `P'` on the side of `K`.  The edges of the loop separate `P'` from `Π_i`, not
from `C`, so `P'` is not in the `Q₀`-class of `C`.  It reaches `o` across the loop and `Π_i`, so it
is not a lake of `L_C` either.  So the outside walk of the fill of `L_C` skips the loop.  The `G₁`
run then splits into two sub-arcs, and no `CyclicArc` `A₁` reads it.
* So `PocketFourPieceInsideStatement` does **not** follow from `PocketLabelNoninterleavingStatement`
  plus list and arc glue.
* Also, the lake fill can hold `Π_i` and `Π_j` (lane gl-p07-20a, wedge model), which breaks the
  inside clause.

The witness has to be the piece of `C` together with its sub-pockets `P'` and its lakes inside
`sideFaces K`, cut down to `sideFaces K`.

## The residual (`PocketFourPieceInputProofResidualStatement`)

Under the premise block, with `G₁`, `G₂` universally quantified, there is an enclosed face set
`faces ∋ C` with outside walk `outerWalk` such that:
1. `faces ⊆ sideFaces K.walk`.  This is unconditional; the target only asks for it when
   `A₁ = A₂ = 0`.
2. **Per dart:** for every walk dart `d`, the inside dart `α d` is based on the side of `K`, off
   `a` and `b`, and on an edge of `K`, `∂a` or `∂b`.
3. **The four noninterleaving facts** of `PocketLabelNoninterleavingStatement`, for this walk.
4. **Arc runs:** every block `U` of `invDarts outerWalk` with all entries in `invDarts G₁` is
   `invDarts A.darts` for some `A : CyclicArc (cellDarts X i)`.  The same holds for `G₂`.  A block
   is a prefix of a rotation.

## What the reduction proves (`FourPieceInputProof.lean`)

`pocketFourPieceInside_of_inputProofResidual` proves the target from the residual.
* **Labels:** every entry of `invDarts outerWalk` is in `invDarts G₁` or `invDarts G₂`, or reverses
  a far side.  This comes from clause 2 by `PocketLabel.label_of_pocket` (lane gl-p07-08).
* **The cyclic four-piece order:** `FourPiece.exists_fourPiece`.
* **Blocks as prefixes of rotations,** and then arcs by clause 4.
* **The rotation of the walk:** `SideBound.exists_rotate_invDarts`.
* **Empty blocks give zero-length arcs.**
* **The inside clause,** from clause 1.

## Why the residual is true

This is the route of lane gl-p07-20a's docstring.  Let `P` be the union of the `Q₀`-class of `C`
and of the classes of its sub-pockets.  Take the lake fill of `P` and cut it down to `sideFaces K`.
* **Clause 1** holds by construction.
* **Clause 2.**  A walk dart borders a face of the fill.  Take a boundary edge of a `Q₀`-class, or a
  `K`-edge towards a lake that was cut out.  Either way the edge is `Q₀`, and the inside face is in
  `P`.
* **Clause 3** is gl-p07-17's planarity argument, for this walk instead of `L_C`.
* **Clause 4.**  The sub-pockets are inside, so the walk follows every loop of `G₁`.  Consecutive
  walk darts on `Π_i` are then `facePerm`-consecutive.

**Riskiest point:** clause 4 when a far side of `a` or `b` meets a `Π_i`-loop at a pinch vertex.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Residual of lane gl-p07-20b.**  An inside enclosed face set whose outside walk has pocket
labels, the four noninterleaving facts, and cell arcs for its gap runs.  See the module docstring.
-/
def PocketFourPieceInputProofResidualStatement : Prop :=
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
        ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
            faces ⊆ sideFaces X.toCombMap K.walk ∧
            (∀ d ∈ outerWalk,
              X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
                X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
                (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
                  walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d))) ∧
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
              (invDarts X outerWalk) ∧
            (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
              (invDarts X outerWalk).rotate m = U ++ V →
              (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
              ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
            (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
              (invDarts X outerWalk).rotate m = U ++ V →
              (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
              ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketFourPieceInputProofResidualStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
