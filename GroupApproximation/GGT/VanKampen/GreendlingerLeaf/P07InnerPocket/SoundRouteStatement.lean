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

