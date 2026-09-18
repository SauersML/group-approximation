import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-41: absorption from a card-maximal basic pair

`FourPieceWitness.AbsorbLobeStatement` restates `AbsorbFaceSetStatement` (Base ∧ Improve).  Base
is unchanged.  Improve gains one hypothesis: the basic pair `(faces, outerWalk)` it receives is
**card-maximal** (`AbsorbLobeMaximal`), meaning no basic pair has more faces.

The planar argument has to work only at the top of the absorption order.  There the exposed
pocket face `f = faceOf (α (facePerm g))` cannot be absorbed into any basic pair
(`absorbLobe_not_insert`, in `AbsorbLobeProof.lean`).  So the remaining work is to show that a
maximal pair with failing step clauses has a good basic pair, or that branch 2 holds.  The
card-strict disjunct of Improve is kept in the conclusion.  Under the hypothesis it is
contradictory, and keeping it makes the statement literally weaker than
`AbsorbFaceSetStatement`.

## LOUD: EQUIVALENT to the target as a proposition; Base NOT proved

* `AbsorbFaceSetStatement → AbsorbLobeStatement`: drop the hypothesis.
* `AbsorbLobeStatement → NoPlanarDegenStepStatement`: take a card-maximal basic pair (via
  `absorbFaceSet_iterate`) and apply Improve once.
* `NoPlanarDegenStepStatement → AbsorbFaceSetStatement` is the existing converse.

So all three are equivalent (`absorbLobe_iff_absorbFaceSet`, `absorbLobe_iff_noPlanarDegenStep`).
The statement is weaker only in proof content: one Improve call at a maximal pair replaces the
whole iteration.

**Base is not proved outright.**  It requires the dart clause and the four `CyclicNoInterleave`
clauses for some enclosed walk inside the pocket.  No unconditional source exists in the corpus:
the lake walk of `K.walk` gives the enclosure and `c`, but not noninterleave.

## Why no single-face absorption lemma reduces Improve

A lemma of the shape "absorb `f` (and its lakes) into `F`, getting an enclosed successor walk"
does not imply Improve.  The new pair must also be basic.

* `F' ⊆ sideFaces K.walk` fails when the lake of `f` contains `Π_j`, or any face outside the
  pocket.
* The dart clause fails when the new walk runs along a face in `a.1` or `b.1`.
* Noninterleave is not preserved under absorption.

Base is unproved, so a reduction here has to carry it.  Any Statement `P` with
`P → NoPlanarDegenStepStatement` and `NoPlanarDegenStepStatement → P` is equivalent as a `Prop`.
A strictly weaker reduction, meaning Improve alone, needs Base proved first.

## Truth check

It is true exactly when the target is, and the target is plausibly true (see
`NoPlanarDegenStepStatement.lean`).  The card-strict Improve without the step-good disjunct is
**not** stated.  Under maximality it would say that no maximal pair fails its step clauses unless
branch 2 holds, which is at risk when the lobe behind a `G₁`-loop is not inside the pocket (for
example `Π_j` inside the loop).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Card-maximality of a basic pair**: no basic pair has more faces than `faces`. -/
abbrev AbsorbLobeMaximal {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (c : X.toCombMap.Face) (faces : Finset X.toCombMap.Face) :
    Prop :=
  ∀ (faces' : Finset X.toCombMap.Face) (outerWalk' : List X.toCombMap.Dart),
    AbsorbFaceSetBasic a b K G₁ G₂ c faces' outerWalk' → faces'.card ≤ faces.card

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbLobeMaximal

/-- **Remaining gap of lane gl-p07-41.**  This is `AbsorbFaceSetStatement` with Improve restricted to
card-maximal basic pairs (`AbsorbLobeMaximal`).  See the module docstring. -/
def AbsorbLobeStatement : Prop :=
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
      (¬ ∃ outerWalk : List X.toCombMap.Dart,
          EnclosedFaceSetSucc X (witnessFaces a b K C.face) outerWalk ∧
            ∀ d ∈ outerWalk,
              X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K C.face) →
      ¬ ((∀ f, f ∉ witnessFaces a b K C.face →
          f ∈ PocketNoncrossing.faceClass X.toCombMap
            (boundaryKeep X.toCombMap (witnessFaces a b K C.face)) X.outerFace) ∧
        (PocketOrbit.keepMap X.toCombMap (boundaryKeep X.toCombMap (witnessFaces a b K C.face))
          (boundaryKeep_alpha X.toCombMap (witnessFaces a b K C.face))).IsConnected) →
        ((∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
            AbsorbFaceSetBasic a b K G₁ G₂ C.face faces outerWalk) ∨
          AbsorbFaceSetBranchTwo i j C.face) ∧
        (∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          AbsorbFaceSetBasic a b K G₁ G₂ C.face faces outerWalk →
          ¬ AbsorbFaceSetStepGood G₁ G₂ outerWalk →
          AbsorbFaceSetExposed K G₁ G₂ faces outerWalk →
          AbsorbLobeMaximal a b K G₁ G₂ C.face faces →
          (∃ (faces' : Finset X.toCombMap.Face) (outerWalk' : List X.toCombMap.Dart),
              AbsorbFaceSetBasic a b K G₁ G₂ C.face faces' outerWalk' ∧
                (faces.card < faces'.card ∨ AbsorbFaceSetStepGood G₁ G₂ outerWalk')) ∨
            AbsorbFaceSetBranchTwo i j C.face)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbLobeStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
