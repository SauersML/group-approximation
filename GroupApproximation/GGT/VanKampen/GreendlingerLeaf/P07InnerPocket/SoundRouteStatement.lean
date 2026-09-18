import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcAuditStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlockWitnessAudit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcsAuditPinchStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-31: a sound route to `PocketFourPieceOffStatement`

## Route map (truth marks)

Every `_of_` chain in the corpus that ends in `PocketFourPieceOffStatement`
(`AssemblyStatement.lean`), with each input marked.

* `pocketFourPieceOff_of_inside` (`FourPieceOffCell.lean`): input `PocketFourPieceInsideStatement`,
  UNKNOWN / plausibly true.  The off-cell half is proved (`pocketFourPieceOffCell`).
* `pocketFourPieceOff_of_input_offCell`: the same, with the off-cell half as a hypothesis (proved).
* `pocketFourPieceOff_of_lakeRead` (`FourPieceOff.lean`): input
  `PocketFourPieceLakeReadStatement`, UNKNOWN.
* `pocketFourPieceInside_of_arcAuditResidual`: input `PocketFourPieceArcAuditResidualStatement`,
  UNKNOWN / plausibly true (lanes 21c, 28).
* `pocketFourPieceInside_of_inputProofResidual`: input
  `PocketFourPieceInputProofResidualStatement`, **FALSE** (M2, lane gl-p07-21c).
* `pocketFourPieceArcAuditResidual_of_inputProofResidual`: input **FALSE** (M2).
* `FourPieceWitness.arcAuditResidual_of_planar_noninterleave_arcsAudit`: all three inputs
  **FALSE**: `PocketFourPieceWitnessPlanarStatement` (M7/M8, lane 23),
  `PocketFourPieceWitnessNoninterleaveStatement` (M9, lane 27),
  `FourPieceWitness.ArcsAuditStatement` (M11, also M9/M10, lane 29).
* `FourPieceWitness.arcAuditResidual_of_noPlanarDegenerate_noninterleave_arcsAudit` and
  `..._fourBlock_arcsAudit`: `NoPlanarDegenerateStatement` is UNKNOWN / plausibly true, but the
  other two inputs are **FALSE** (M9 for noninterleave and `FourBlockStatement`, M11 for
  `ArcsAuditStatement`).
* **Proved and used here:** `FourPieceWitness.arcsAuditPinch` (lane 29),
  `pocketFourPieceOffCell`, `dart_clause`, `mem_witnessFaces_self`,
  `witnessFaces_subset_sideFaces`, `pocketFourPieceInside_of_arcAuditResidual`.

**LOUD (confirmed, not new):** every existing chain from `Off` down to witness-level statements
consumes a FALSE input (M2, M8, M9 or M11).  No existing theorem gives `Off` from true inputs
beyond the arc-audit residual.  The consumer of `arcsAuditPinch` needs pinch-freeness, and the
consumer of the noninterleaving reading needs nondegenerate contact arcs.  Neither is a premise
of `PocketFourPieceOffStatement`, so this lane splits into cases.

## The case split

Under the premise block of the arc-audit residual, put `F = witnessFaces a b K C.face`.  **Case
(i)** is the conjunction of:
* all four contact arcs are nonempty (`0 < (a.cellArcList i).length`, and so on);
* every dart of `G₁` and of `G₂` is `PocketRun.PinchFreeAt`;
* `F` has a bridge-free successor outside walk.

In case (i) branch 1 of the residual is built with `faces = F`.  Clauses 4a and 4b come from the
PROVED `arcsAuditPinch`.  The pinch bound of 4b holds vacuously, since no dart is pinched.  Only
clause 3 (the four noninterleaving facts) is not proved.  **Case (ii)** is its negation.

## The residual (`SoundRoute.PinchCaseStatement`)

One statement, under the premise block of the arc-audit residual, with two clauses:
1. **(read)** in case (i), for every witness walk, the four noninterleaving facts;
2. **(rest)** if case (i) fails, the arc-audit residual's conclusion.

**Strictly smaller.**
* Clause (read) is `FourPieceWitness.NoninterleaveNondegStatement` (lane 27) with two extra
  pinch-free hypotheses.
* Clause (rest) is the arc-audit residual with the extra hypothesis `¬ case (i)`.
* So `ArcAuditResidual ∧ NoninterleaveNondeg` gives it by dropping hypotheses
  (`SoundRoute.pinchCase_of_arcAuditResidual_noninterleaveNondeg`).
* It also gives lane 28's `NoPlanarDegenerateStatement`
  (`SoundRoute.noPlanarDegenerate_of_pinchCase`), since "no witness walk" implies `¬ case (i)`.
* The 4a/4b content of case (i) is discharged by the proved `arcsAuditPinch` and is not in the
  residual.

## Truth check

* **M2 (crescent, lane 21c).**  The last dart `x` of `λ ⊆ G₁` is pinched, so case (ii).  (read)
  is vacuous.  (rest) holds through branch 2: `faces = {C}` and the walk is `λ`, one cell arc
  of `i`.
* **M8 (empty-arc island, lane 23).**  `a.cellArcList i = []` and there is no witness walk, so
  case (ii).  (read) is vacuous.  (rest) holds through branch 1 with `faces = P' ∪ a.1`; the
  walk reads `Ḡ₁ · B̄ · Ḡ₂` (lane 28 truth check).
* **M9 (a disc `a.1` in the middle of `G₁`, lane 27).**  `a.cellArcList i = []`, so case (ii),
  although a witness walk exists.  (read) is vacuous, which is exactly how M9 refuted the
  unrestricted noninterleave statement.  (rest) holds through branch 1 with
  `faces = sideFaces K.walk = P₀ ∪ a.1`: the walk reads `Ḡ₁ · Ḡ₂ · B̄`, a four-block word, and
  4a/4b hold at contiguous `G₁`/`G₂` blocks.
* **M11 (a lobe inside a third `G₁`-loop, lane 29).**  `λ_end` is not pinch-free, so case (ii).
  (read) is vacuous.  (rest) holds through branch 2: `faces = {C}` (the `λ`-disc), walk `λ`,
  one cell arc of `i`.

No model refutes either clause.  **Riskiest point:** clause (rest) at pinch pathologies where `C`
is not enclosed by a single loop of `Π_i`, so branch 2 is unavailable.  This is the same risk
lanes 21c and 28 recorded for the arc-audit residual.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Residual of lane gl-p07-31.**  Under the premise block of
`PocketFourPieceArcAuditResidualStatement`:
* **(read)** for nondegenerate candidates, pinch-free `G₁` and `G₂`, and every bridge-free successor
  outside walk of `witnessFaces a b K C.face`, the four noninterleaving facts hold;
* **(rest)** outside that case, the arc-audit residual's conclusion holds.

See the module docstring for the route, why it is strictly smaller, and the truth check. -/
def PinchCaseStatement : Prop :=
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
        (0 < (a.cellArcList i).length → 0 < (a.cellArcList j).length →
          0 < (b.cellArcList i).length → 0 < (b.cellArcList j).length →
          ∀ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk →
            (∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
              FourPieceWitness.witnessFaces a b K C.face) →
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) →
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) →
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
                (invDarts X outerWalk)) ∧
        (¬ (0 < (a.cellArcList i).length ∧ 0 < (a.cellArcList j).length ∧
            0 < (b.cellArcList i).length ∧ 0 < (b.cellArcList j).length ∧
            (∀ d ∈ G₁.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            (∀ d ∈ G₂.darts, PocketRun.PinchFreeAt X.toCombMap d) ∧
            ∃ outerWalk : List X.toCombMap.Dart,
              EnclosedFaceSetSucc X (FourPieceWitness.witnessFaces a b K C.face) outerWalk ∧
                ∀ d ∈ outerWalk, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
                  FourPieceWitness.witnessFaces a b K C.face) →
          (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
            EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
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
                (invDarts X outerWalk) ∧
              (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
                (invDarts X outerWalk).rotate m = U ++ V →
                (∀ e ∈ U, e ∈ invDarts X G₁.darts) →
                (∃ e ∈ V, e ∉ invDarts X G₁.darts) →
                ∃ A : CyclicArc (cellDarts X i), U = invDarts X A.darts) ∧
              ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₁.darts) →
                ∃ (n : ℕ) (A : CyclicArc (cellDarts X i)),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∧
              (∀ (m : ℕ) (U V : List X.toCombMap.Dart),
                (invDarts X outerWalk).rotate m = U ++ V →
                (∀ e ∈ U, e ∈ invDarts X G₂.darts) →
                (∃ e ∈ V, e ∉ invDarts X G₂.darts) →
                ∃ A : CyclicArc (cellDarts X j), U = invDarts X A.darts) ∧
              ((∀ e ∈ invDarts X outerWalk, e ∈ invDarts X G₂.darts) →
                ∃ (n : ℕ) (A : CyclicArc (cellDarts X j)),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts)) ∨
          (∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart) (n : ℕ),
            EnclosedFaceSetSucc X faces outerWalk ∧ C.face ∈ faces ∧
              ((∃ A : CyclicArc (cellDarts X i),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts) ∨
                (∃ A : CyclicArc (cellDarts X j),
                  invDarts X (outerWalk.rotate n) = invDarts X A.darts))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute.PinchCaseStatement

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SoundRoute
