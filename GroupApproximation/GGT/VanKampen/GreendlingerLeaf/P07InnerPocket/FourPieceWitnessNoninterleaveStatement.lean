import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitnessRead
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-24: the four-block reading of the witness outside walk

Lane gl-p07-24.  The target is `PocketFourPieceWitnessNoninterleaveStatement` (clause 3,
`FourPieceWitnessRead.lean`) for `F = FourPieceWitness.witnessFaces a b K C.face`
(`FourPieceWitnessDef.lean`).  The context is Osin, arXiv:math/0411039v3, §9, proof of Lemma
9.7(b).  This file states the residual.  `FourPieceWitnessNoninterleaveEndpoint.lean` proves the
target from it.

## Notation

`l = invDarts X outerWalk`, for a bridge-free outside walk of `F` that turns to its successor.
Four priority classes on darts `e`:
* `G1`: `e ∈ invDarts G₁`;
* `G2`: `e ∉ invDarts G₁` and `e ∈ invDarts G₂`;
* `B`: in neither, and `α e ∈ b.sideFrom i`;
* `A`: in neither, and `α e ∉ b.sideFrom i`.

## The residual (`FourPieceWitness.FourBlockStatement`)

Under the premise block of the target, some rotation of `l` reads `U₁ ++ U₂ ++ U₃ ++ U₄`, where:
* `U₁` lies in `G1` and `U₃` lies in `G2`;
* `U₂` and `U₄` both lie outside `G1` and `G2`;
* either `U₂ ⊆ B` and `U₄ ⊆ A`, or `U₂ ⊆ A` and `U₄ ⊆ B`.

The blocks may be empty.  The conclusion is the one of `PocketLabelFourBlockStatement`
(`NoninterleaveStatement.lean`), for the walk of `F` instead of the lake-fill walk.

## Why this is not a specialization of `PocketLabelFourBlockStatement`

That statement is about an outside walk of `absorbed (sideFaces L) X.outerFace`, where `L` is the
orbit of the `Q₀`-class of `C`.  The witness `F` is a different face set.
* **Lens model.**  `Π_i` and `Π_j` touch at two vertices `v`, `w`, and `C` is in the left
  sub-pocket.  The lens between them borders only `Π_i` and `Π_j`, so it is open and touches `C`'s
  sub-pocket at `v`.  Hence the lens is in `F`.  It is not a lake of `L`: it shares the edges of
  `G₁` with `Π_i`, which lies in the outer component.
* So the two outside walks differ, and no rewriting turns one hypothesis into the other.

## Truth check

**TRUE; no counter-model found.**

**Step 1: every entry of `l` is in one of the four arcs of the pocket curve.**  Take `e ∈ l`, so
`faceOf e ∈ F` and `α e` is kept (`FourPieceWitness.dart_clause`).
* `faceOf e ∈ sideFaces K`, and `faceOf e` is in neither `a` nor `b`.
* The walk darts are exactly the boundary darts of `sideFaces K`
  (`isBoundaryDart_sideFaces_iff`).  Hence:
  * `α e ∉ K.walk`;
  * `Π_i, Π_j ∉ sideFaces K`, since `firstArc` and `secondArc` are nonempty;
  * the region-cycle darts have their face in their region.
* The only remaining cases are `α e ∈ G₁`, `α e ∈ G₂`, `α e ∈ b.sideFrom i` and
  `α e ∈ a.sideFrom j`.
* So the reversed walk reads edges of the pocket curve `Γ = Ḡ₁ · ā_j · Ḡ₂ · b̄_i` only.

**Step 2: `l` is `Γ` with cyclic intervals deleted.**
* `F` is a union of edge-components ("sub-pockets") of the pocket, joined at vertices.
* At a vertex, the orbit of `F` turns along a corner of the complement of `F`.  The pocket curve
  turns along a corner of `Π_i`, `Π_j`, `a` or `b` (consecutive `G₁` darts share a `Π_i` corner,
  and so on).
* So `l` either follows `Γ`, or skips the boundary of a sub-pocket off `F` attached at that vertex.
  That boundary is a loop of `Γ`, which is a cyclic interval.
* The skips nest, since the sub-pockets form a planar tree through their pinch vertices.
* Deleting cyclic intervals from the four-block word `G1 A G2 B` leaves a four-block word, in one
  of the two orientations.

**Models.**
* *Self-pinch of `Π_i`* (`G₁ = G₁a λ G₁b` with a loop `λ` at `v`):
  * `C` in the main sub-pocket: the loop sub-pocket is open and in `F`, and `l = Ḡ₁ ā Ḡ₂ b̄`;
  * `C` inside `λ`: the main sub-pocket borders `a` and is cut, so `l = λ̄`, one block.
* *Pinch of the two far sides* (`a_j` and `b_i` meet at `v`): the sub-pocket off `C` borders `a`
  or `b` and is cut.  `l` is `B̄₂ Ḡ₁ Ā₁` or `Ā₂ Ḡ₂ B̄₁`.
* *`Π_i` touching the far side of `a`* at `v`: the loop `G₁b · A₁` is read in order if `C` is
  inside it.  Otherwise it is cut.
* *Lens* (above): `C` in the left sub-pocket gives `l = Ḡ₁L Ḡ₁M · Ḡ₂M Ḡ₂L · Ā`.  `C` in the lens
  gives `l = Ḡ₁M Ḡ₂M`.  Both are four blocks.
* *Corner pinch with `B` empty* (`Π_i` touches the `a/Π_j` corner `p`): `F` is both sub-pockets.
  The orbit turns `Ḡ₁a → Ḡ₁b` along the `Π_i` corner, and `Ā → Ḡ₂` along the `a … Π_j` corner.
* *`a` and `b` sharing a pocket edge:* the pocket splits.  `l = Ḡ₁ Ā₁ B̄₂` has three blocks.
* *M2 crescent* (`FourPieceArcAuditStatement.lean`): `F = {C}` and `l = λ̄` lies in `G1`.  Take
  `U₁ = l`.
* *M6* (an `a`-lobe behind a `G₁`-loop edge): `l = λ̄ · Ā'`, two blocks.
* *M7* (the `a/Π_j/b` blob behind the pinch): if a bridge-free successor walk of `F` exists, it is
  the figure eight `λ̄ · (Ā Ḡ₂ B̄)`, four blocks.  Otherwise the statement is vacuous.
* *Wedge:* vacuous, since `houter` fails.

**Riskiest point:** step 2 at a vertex where an empty contact arc meets a pinch of `Π_i`.  The
checked corner-pinch model is the worst case found.

## Why it is strictly smaller, and not a restatement

* **Strictly stronger as a conclusion, so not equivalent.**  The cyclic word `G2 A G1 A`
  satisfies all four noninterleaving facts but has no four-block form.
* **Strictly less proof content.**  The residual keeps only the planar reading step (step 2).  The
  class bookkeeping and the derivation of the four `CyclicNoInterleave` facts are proved
  (`FourPieceWitness.fourNoninterleave_of_blocks`, `FourPieceWitnessNoninterleaveList.lean`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Residual of lane gl-p07-24: the witness outside walk reads four blocks.**  A rotation of
`invDarts X outerWalk` is `U₁ ++ U₂ ++ U₃ ++ U₄`, with `U₁ ⊆ Ḡ₁` and `U₃ ⊆ Ḡ₂` (off `Ḡ₁`).  The
blocks `U₂`, `U₄` are off both, and one of them reverses the b far side while the other does not.
See the module docstring for why it is true and smaller. -/
def FourBlockStatement : Prop :=
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
        EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk →
        (∀ d ∈ outerWalk,
          X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.FourBlockStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
