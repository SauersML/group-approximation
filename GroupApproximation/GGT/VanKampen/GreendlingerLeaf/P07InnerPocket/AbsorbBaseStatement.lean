import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbBaseDart
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-46: Base outside the lake-filled case

`FourPieceWitness.AbsorbBaseStatement` restates `AbsorbFaceSetStatement` (Base ∧ Improve) with the
same premise block.  Improve is unchanged.  Base is asked for **only when the lake-filled case
`AbsorbBaseCase a b K G₁ G₂ C.face` fails**.  In that case Base is proved
(`absorbBase_basic_of_case`, `AbsorbBaseDart.lean`).  The case holds when the lake-filled witness
`F₁ = absorbed F₀ o` of `F₀ = witnessFaces a b K C.face`:
* is inside the pocket, `F₁ ⊆ sideFaces K.walk`, and
* has a bridge-free enclosed successor walk `ow` satisfying the four noninterleave clauses.

## LOUD: EQUIVALENT to the target as a proposition; Base NOT proved outright

* `AbsorbFaceSetStatement → AbsorbBaseStatement`: drop the case hypothesis.
* `AbsorbBaseStatement → AbsorbFaceSetStatement`: split on the case, using
  `absorbBase_basic_of_case`.

So the two statements are equivalent (`absorbBase_iff_absorbFaceSet`, `AbsorbBaseProof.lean`).  The
new statement is smaller in proof content, not weaker as a `Prop`: Base is discharged whenever the
lake-filled witness works.

**Why Base is not proved outright.**  The premise `hno` rules out the witness walk itself.  What
remains open for the lake-filled witness `F₁` is:
1. `F₁ ⊆ sideFaces K.walk`.  A lake of `F₀` can contain faces outside the pocket, such as `Π_j`
   inside a `G₁`-loop, or a component of `sideOutside K.walk` that is fenced off by `F₀`.  Ruling
   this out needs the outer Euler hypothesis (connectivity of `sideOutside`), and the corpus has no
   lemma turning that into dual connectivity.
2. An enclosed successor walk for `F₁`.  `exists_enclosedFaceSetSucc_of_connected` needs
   connectivity of the keep map of `F₁`, and this is not available.
3. The four noninterleave clauses.  These fail for the lake-filled witness in model M9-with-hole
   (`NoPlanarDegenStepStatement.lean`).  There a different face set, or branch 2, is needed.

## Truth check (paper, small models of `NoPlanarDegenStepStatement.lean`)

* M8 (empty-arc island): the witness is an annulus around the island `a.1`, so there is no walk
  and `hno` holds.  Filling the island gives `F₁ = P' ∪ a.1 ⊆ sideFaces K.walk`, which is the
  branch-1 face set of lane 28.  Its walk `Ḡ₁ · B̄ · Ḡ₂` is bridge-free and satisfies N.  The case
  holds and Base is proved.
* M9-with-hole: `F₁` is enclosed, but its walk interleaves `G₁` with the rest, so N fails.  The case
  fails and Base must come from elsewhere.  This matches the note "lake-filled witness alone fails
  clause 3".
* Otherwise the statement is true exactly when the target is, since the two are equivalent.  The
  target is plausibly true (see `NoPlanarDegenStepStatement.lean`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **Remaining gap of lane gl-p07-46.**  This is `AbsorbFaceSetStatement` with Base asked for only
outside the lake-filled case `AbsorbBaseCase`.  See the module docstring. -/
def AbsorbBaseStatement : Prop :=
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
        (¬ AbsorbBaseCase a b K G₁ G₂ C.face →
          (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
              AbsorbFaceSetBasic a b K G₁ G₂ C.face faces outerWalk) ∨
            AbsorbFaceSetBranchTwo i j C.face) ∧
        (∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
          AbsorbFaceSetBasic a b K G₁ G₂ C.face faces outerWalk →
          ¬ AbsorbFaceSetStepGood G₁ G₂ outerWalk →
          AbsorbFaceSetExposed K G₁ G₂ faces outerWalk →
          (∃ (faces' : Finset X.toCombMap.Face) (outerWalk' : List X.toCombMap.Dart),
              AbsorbFaceSetBasic a b K G₁ G₂ C.face faces' outerWalk' ∧
                (faces.card < faces'.card ∨ AbsorbFaceSetStepGood G₁ G₂ outerWalk')) ∨
            AbsorbFaceSetBranchTwo i j C.face)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbBaseStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
