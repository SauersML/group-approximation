import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WalkDegenStepStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-39b: the walk-degenerate residual by cases and absorption

The target is `PinchCase.WalkDegenStepStatement` (`WalkDegenStepStatement.lean`, lane gl-p07-37c).
This file states the residual `PinchCase.WalkDegenCaseStatement`.  `WalkDegenCaseProof.lean`
proves the target from it (`PinchCase.walkDegenCase_step`) and the converse.  Certifies no printed
sentence.

## The case split

Write `F = witnessFaces a b K C.face` and `ow` for its witness walk.  The failure hypothesis
`hbad` says that the four noninterleave clauses (N) and the four step clauses S1a, S1b, S2a, S2b
do not all hold for `ow`.
* **Case N holds** (so a step clause fails; models M11, P2).  The witness pair `(F, ow)` is a
  *basic* pair in the sense of lane gl-p07-38 (`FourPieceWitness.AbsorbFaceSetBasic`).  This is
  proved outright (`walkDegenCase_witness_basic`, `WalkDegenCaseBase.lean`): `C.face ∈ F`
  (`mem_witnessFaces_self`), `F ⊆ sideFaces K.walk`, the dart clause (`dart_clause`, from the
  bridge-free hypothesis), and N.  So no Base is asked for in this case.
* **Case N fails** (model M9).  The residual asks for a basic pair or branch 2 (Base).  No step
  clause is required.
* **Both cases.**  The residual asks for lane 38's Improve step.  A basic pair whose step clauses
  fail comes with an exposed gap dart (`absorbFaceSet_exposed_of_basic`, proved).  It must be
  grown strictly, or made good, or branch 2 must hold.  Here Improve receives the whole
  walk-degenerate premise block, including the witness walk and `hbad`.

The iteration and its termination are lane 38's `absorbFaceSet_iterate`, reused.

## LOUD: equivalent as a Prop, strictly smaller in proof content

A good pair of the target serves as Base and as every Improve step, and branch 2 serves both.  So
the target implies the residual (`walkDegenCase_of_step`), and the two are **equivalent**
(`walkDegenCase_iff_step`).  No strictly weaker cut with a closed consistent case was found:
* every consistent case needs a NEW face set with its enclosed walk (37c's docstring shows that
  the witness walk alone never gives branch 1 or branch 2);
* the corpus has no construction of such a set (lake-fills of noncrossing walks need
  `FollowsBoundary` or the Q₀-orbit, and `sideFaces K.walk` fails the dart clause on nondegenerate
  contacts, `noWalkAbsorb_left_false`).
The proof content removed, compared with the target: Base on the consistent case N (M11, P2);
Base never needs the step clauses; the iteration, the termination, the exposed dart and the
reassembly of the thirteen clauses are all proved.

## Truth check (paper)

Plausibly TRUE: it is equivalent to the target, which no model refutes (37c's docstring).
* **M9.**  N fails.  Base: `sideFaces K.walk` with its walk (37c's reading), or the lobe-absorbed
  witness.
* **M11.**  N holds, S1a fails at `λ_end`.  Improve returns branch 2 with `faces = {C}`.
* **P2.**  N holds, S1b fails (two junctions).  Improve returns branch 2 with `faces = F ∪ R₁`.
* **Riskiest point** (unchanged from lanes 31, 34, 38): Improve when the lobe behind a `G₁`-loop
  is not inside the pocket (for example `Π_j` inside the loop).  There the `S F' ow'` disjunct or
  branch 2 must carry the step.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The four noninterleave clauses (N) for a walk**, verbatim from `WalkDegenStepStatement`. -/
abbrev WalkDegenCaseNoninterleave {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (b : RegionCandidate D eps X)
    (G₁ : CyclicArc (cellDarts X i)) (G₂ : CyclicArc (cellDarts X j))
    (outerWalk : List X.toCombMap.Dart) : Prop :=
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.WalkDegenCaseNoninterleave

/-- **Remaining gap of lane gl-p07-39b.**  The premise block of `WalkDegenStepStatement`,
verbatim.  Then Base, but only when the witness walk fails a noninterleave clause (N); and
Improve, lane 38's absorption step.  See the module docstring. -/
def WalkDegenCaseStatement : Prop :=
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
        (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
          FourPieceWitness.witnessFaces a b K C.face) →
        ¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d)) →
        ¬ (FourPiece.CyclicNoInterleave (fun e => e ∈ invDarts X G₁.darts)
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
                  PocketRun.PinchFreeAt X.toCombMap outerWalk[q]) → p = q)) →
          (¬ WalkDegenCaseNoninterleave b G₁ G₂ outerWalk →
              ((∃ (faces : Finset X.toCombMap.Face) (ow : List X.toCombMap.Dart),
                  FourPieceWitness.AbsorbFaceSetBasic a b K G₁ G₂ C.face faces ow) ∨
                FourPieceWitness.AbsorbFaceSetBranchTwo i j C.face)) ∧
            (∀ (faces : Finset X.toCombMap.Face) (ow : List X.toCombMap.Dart),
              FourPieceWitness.AbsorbFaceSetBasic a b K G₁ G₂ C.face faces ow →
              ¬ FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ ow →
              FourPieceWitness.AbsorbFaceSetExposed K G₁ G₂ faces ow →
              (∃ (faces' : Finset X.toCombMap.Face) (ow' : List X.toCombMap.Dart),
                  FourPieceWitness.AbsorbFaceSetBasic a b K G₁ G₂ C.face faces' ow' ∧
                    (faces.card < faces'.card ∨
                      FourPieceWitness.AbsorbFaceSetStepGood G₁ G₂ ow')) ∨
                FourPieceWitness.AbsorbFaceSetBranchTwo i j C.face)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase.WalkDegenCaseStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchCase
