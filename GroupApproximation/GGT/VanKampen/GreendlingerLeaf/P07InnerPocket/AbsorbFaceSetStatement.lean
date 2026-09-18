import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoPlanarDegenStepStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-38: the target as an absorption iteration

`FourPieceWitness.NoPlanarDegenStepStatement` asks for one face set with an outer walk that meets
a basic block of clauses (enclosed successor walk, `C`, inside the pocket, the dart clause, the four
noninterleave clauses) and also the four local step clauses S1a, S1b, S2a, S2b.  The planar
mechanism described in its docstring is to absorb holes, lakes and lobes behind `G`-loops.
`FourPieceWitness.AbsorbFaceSetStatement` splits that mechanism into two parts.

* **Base.**  Some basic pair exists, or branch 2 holds.  No step clause is required, so the holes
  and lakes can be filled without regard to pinches.
* **Improve.**  Take a basic pair `(F, ow)` whose step clauses fail.  It comes with an exposed
  dart (`AbsorbFaceSetExposed`): `g ∈ ow` on `G₁` (or `G₂`) with `facePerm g` on the same gap but
  off the walk, and the face across `facePerm g` lies in `sideFaces K.walk` but not in `F`.
  Return a basic pair that has strictly more faces or satisfies the step clauses, or return
  branch 2.

The termination (`absorbFaceSet_iterate`, measure `#faces` bounded by `Fintype.card Face`), the
derivation of the exposed dart from the failure of the step clauses, and the reassembly of the
thirteen target clauses are proved in `AbsorbFaceSetProof.lean`.

## LOUD: EQUIVALENT to the target as a proposition

The Improve disjunct `S F' ow'` accepts any good pair, so the target implies the statement
(`absorbFaceSet_of_noPlanarDegenStep`).  The statement is therefore not weaker as a `Prop`:
`absorbFaceSet_iff_noPlanarDegenStep`.  It is smaller in proof content.  Base drops the four step
clauses.  Improve receives a basic pair, the failure of its step clauses, and an explicit
absorption candidate `faceOf (α (facePerm g)) ∈ sideFaces K.walk \ F`.  Iteration, termination,
closure and the step-clause derivation from closure (`noWalkAbsorb_step_of_closed`,
`noWalkAbsorb_unique_of_closed`) are done.

## Truth check

It is true exactly when the target is, and the target is plausibly true (see
`NoPlanarDegenStepStatement.lean`).  A strictly weaker variant was rejected: the card-strict
Improve without the `S F' ow'` disjunct.  The target does not imply it, and it is at risk when
the lobe `L` behind a `G₁`-loop is not inside the pocket (for example `Π_j` inside the loop).
Then no single absorption step stays inside `sideFaces K.walk`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- **The basic clauses of branch 1 of the target**: all but the four local step clauses. -/
abbrev AbsorbFaceSetBasic {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X)
    (K : CellPocketWalk D eps X i j) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) (c : X.toCombMap.Face) (faces : Finset X.toCombMap.Face)
    (outerWalk : List X.toCombMap.Dart) : Prop :=
  EnclosedFaceSetSucc X faces outerWalk ∧ c ∈ faces ∧
    faces ⊆ sideFaces X.toCombMap K.walk ∧
    (∀ d ∈ outerWalk,
      X.toCombMap.alpha d ∈ invDarts X G₁.darts ∨
      X.toCombMap.alpha d ∈ invDarts X G₂.darts ∨
      (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap K.walk ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 ∧
        (walkKeep X.toCombMap K.walk (X.toCombMap.alpha d) ∨
          walkKeep X.toCombMap a.2.boundary.cycle (X.toCombMap.alpha d) ∨
          walkKeep X.toCombMap b.2.boundary.cycle (X.toCombMap.alpha d)))) ∧
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbFaceSetBasic

/-- **The four local step clauses S1a, S1b, S2a, S2b of the target.** -/
abbrev AbsorbFaceSetStepGood {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {i j : Fin X.rCellCount} (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (outerWalk : List X.toCombMap.Dart) : Prop :=
  ((∃ d ∈ outerWalk, d ∉ G₁.darts) →
    ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₁.darts →
      outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
        (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₁.darts →
      walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
  ((∀ d ∈ outerWalk, d ∈ G₁.darts) →
    ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
      ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
      ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
        PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q) ∧
  ((∃ d ∈ outerWalk, d ∉ G₂.darts) →
    ∀ (p : ℕ) (hp : p < outerWalk.length), outerWalk[p] ∈ G₂.darts →
      outerWalk[(p + 1) % outerWalk.length]'(Nat.mod_lt _
        (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ G₂.darts →
      walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) ∧
  ((∀ d ∈ outerWalk, d ∈ G₂.darts) →
    ∀ (p q : ℕ) (hp : p < outerWalk.length) (hq : q < outerWalk.length),
      ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap outerWalk[p]) →
      ¬ (walkKeep X.toCombMap outerWalk (X.toCombMap.facePerm outerWalk[q]) ∨
        PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbFaceSetStepGood

/-- **Branch 2 of the target**, for the face `c`. -/
abbrev AbsorbFaceSetBranchTwo {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    (i j : Fin X.rCellCount) (c : X.toCombMap.Face) : Prop :=
  ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
    EnclosedFaceSetSucc X faces outerWalk ∧ c ∈ faces ∧
      ((∃ A : CyclicArc (cellDarts X i),
          invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
        (∃ A : CyclicArc (cellDarts X j),
          invDarts X (outerWalk.rotate n) = invDarts X A.darts))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbFaceSetBranchTwo

/-- **An exposed gap dart**: a walk dart `g` on `G₁` (or `G₂`) whose face successor stays on the
same gap but leaves the walk.  The face across that successor is a pocket face outside `faces`,
which is the natural absorption candidate. -/
abbrev AbsorbFaceSetExposed {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (K : CellPocketWalk D eps X i j)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) : Prop :=
  ∃ g ∈ outerWalk,
    ((g ∈ G₁.darts ∧ X.toCombMap.facePerm g ∈ G₁.darts) ∨
      (g ∈ G₂.darts ∧ X.toCombMap.facePerm g ∈ G₂.darts)) ∧
    X.toCombMap.facePerm g ∉ outerWalk ∧
    X.toCombMap.alpha (X.toCombMap.facePerm g) ∉ outerWalk ∧
    X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.facePerm g)) ∉ faces ∧
    X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.facePerm g)) ∈
      sideFaces X.toCombMap K.walk

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbFaceSetExposed

/-- **Remaining gap of lane gl-p07-38.**  Under the premise block of
`NoPlanarDegenStepStatement`: a basic pair exists or branch 2 holds (Base), and every basic pair
with failing step clauses and an exposed gap dart can be grown strictly or made good, or branch 2
holds (Improve).  See the module docstring. -/
def AbsorbFaceSetStatement : Prop :=
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
          (∃ (faces' : Finset X.toCombMap.Face) (outerWalk' : List X.toCombMap.Dart),
              AbsorbFaceSetBasic a b K G₁ G₂ C.face faces' outerWalk' ∧
                (faces.card < faces'.card ∨ AbsorbFaceSetStepGood G₁ G₂ outerWalk')) ∨
            AbsorbFaceSetBranchTwo i j C.face)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.AbsorbFaceSetStatement

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
