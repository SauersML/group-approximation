import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinPiece
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinCoreStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell-bound region choice with the shared-arc bound supplied

Lane gl-p10-79.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The shared-arc bound

`roseLobeOsinPiece_SharedArcBound X μ` says: whenever distinct relator cells `i ≠ j` share a
boundary arc `a :: A` (cell `i` rotated reads `a :: (A ++ S)`, cell `j` rotated reads
`T ++ (a :: A).reverse.map α`), then `|a :: A| < μ · |cell i|`.

`roseLobeOsinPiece_sharedArcBound_of`: the cell bounds and `X.LeastArea` give it.  For each
shared arc, piece (1) (`roseLobeOsinPiece_isPiece`, module `OsinPiece`) makes `ℓ(a :: A)` an
`ε`-piece of `ℓ(a :: (A ++ S))`.  Here `W` is closed under `revInv` and rotation, and the
genericity clause `listVal v' ≠ y · listVal v · y⁻¹` comes from least area through the
two-cell cancellation surgery (`roseLobeOsinPiece_merge_ne_one`).  The `pieces` clause of the
cell bounds then gives the length bound (`roseLobeOsinPiece_sharedArc_lt`).

## The residual

`roseLobeOsinPiece_Statement` is `roseLobeOsinCore_Statement` with the premise
`roseLobeOsinPiece_SharedArcBound X μ` inserted right after `X.LeastArea`.

* `roseLobeOsinPiece_core_of`: the residual implies the core statement, with the same
  thresholds.  The new premise is supplied by `roseLobeOsinPiece_sharedArcBound_of hB hlea`.
* `roseLobeOsinPiece_of_core`: the core statement implies the residual, by dropping the premise.

**LOUD: strength.**  The residual is LOGICALLY EQUIVALENT to `roseLobeOsinCore_Statement` (both
directions are proved here).  It is NOT logically weaker.  It is STRICTLY SMALLER IN PROOF
CONTENT: a proof of the residual may use the shared-arc bound for free, and that bound is the
pieces-small-at-shared-arcs step, including the cancellable-pair exclusion from least area.
That step was item 1 of the remaining gap of `roseLobeOsinCore_Statement`, and it is now
proved.

## Truth check (LOUD)

`roseLobeOsinPiece_Statement` is OPEN, not refuted.  Its truth is exactly that of
`roseLobeOsinCore_Statement`, by the two reductions.

* The long/qg/pieces audit recorded in `OsinCoreStatement` (the gl-p10-72 family, 1260
  configurations, all killed by long + qg + pieces) is unchanged, since the added premise is a
  consequence of the others.
* The caveat "genericity clause of `IsPiece` not modelled" in that audit is now discharged
  for arcs shared by two distinct cells: those arcs ARE pieces, or the diagram is not least
  area.
* A STRONGER variant is NOT stated: it would drop the `pieces` clause from the cell bounds and
  keep only the shared-arc bound.  The audit supports it only partially.  Its `pc_kill` also
  counts arcs shared by one cell with itself at a different position, which the shared-arc
  bound does not cover.

## Remaining gap

`roseLobeOsinPiece_Statement` itself.  Of the gap of `roseLobeOsinCore_Statement`, the
following remain:

1. arcs shared by a cell with itself (`i = j`), which are not covered here;
2. pieces through nontrivial connectors (`ε`-close arcs joined through G-cells), which are
   still read from the `pieces` clause;
3. the general piece / length count over the pocket.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The shared-arc bound** of a diagram `X`: an arc `a :: A` shared by distinct relator
cells `i ≠ j` (read forwards on cell `i`, backwards on cell `j`) has fewer than `μ · |cell i|`
darts. -/
def roseLobeOsinPiece_SharedArcBound {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W) (mu : ℝ) : Prop :=
  ∀ i j : Fin X.rCellCount, i ≠ j → ∀ (n m : ℕ) (a : X.toCombMap.Dart)
    (A S T : List X.toCombMap.Dart), (cellDarts X i).rotate n = a :: (A ++ S) →
      (cellDarts X j).rotate m = T ++ (a :: A).reverse.map X.toCombMap.alpha →
        ((a :: A).length : ℝ) < mu * ((cellDarts X i).length : ℝ)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_SharedArcBound

/-- **The shared-arc bound from the cell bounds and least area** (piece (1) and `pieces`). -/
theorem roseLobeOsinPiece_sharedArcBound_of {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hB : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho) (hlea : X.LeastArea) :
    roseLobeOsinPiece_SharedArcBound X mu :=
  fun _ _ hij _ _ _ _ _ _ hi hj => roseLobeOsinPiece_sharedArc_lt hB hlea hij hi hj

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_sharedArcBound_of

/-- **The cell-bound region choice with the shared-arc bound supplied** (OPEN, not refuted;
LOGICALLY EQUIVALENT to `roseLobeOsinCore_Statement`, STRICTLY SMALLER IN PROOF CONTENT; see
the module docstring).  `roseLobeOsinCore_Statement` with the extra premise
`roseLobeOsinPiece_SharedArcBound X μ` after `X.LeastArea`. -/
def roseLobeOsinPiece_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
            roseLobeOsinCore_CellBounds D W X eps mu lambda c rho → X.LeastArea →
              roseLobeOsinPiece_SharedArcBound X mu →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
                  K.sourceArc.length < (cellDarts X K.source).length →
                  K.targetArc.length < (outerDarts X).length →
                  ¬Unpinched X.toCombMap K.faces →
                  P10ChordLift.AllNonFirstTurnsCrossed K →
                  (walkMap X.toCombMap K.boundary.cycle).IsPlanar →
                  (∀ x y : (walkMap X.toCombMap K.boundary.cycle).Dart,
                    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
                      (walkKeep X.toCombMap K.boundary.cycle)) x.1 y.1 ↔
                      (walkMap X.toCombMap K.boundary.cycle).faceOf x =
                        (walkMap X.toCombMap K.boundary.cycle).faceOf y) →
                  (∀ x : X.toCombMap.Dart, ∃ y, walkKeep X.toCombMap K.boundary.cycle y ∧
                    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
                      (walkKeep X.toCombMap K.boundary.cycle)) x y) →
                  (∀ x y : X.toCombMap.Dart, Relation.EqvGen (CombMap.FaceClassStep
                      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) x y →
                    (X.toCombMap.faceOf x ∈ K.faces ↔ X.toCombMap.faceOf y ∈ K.faces)) →
                  (∀ d ∈ invDarts X K.sourceArc.darts,
                    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face) →
                  (∀ d ∈ K.targetArc.darts,
                    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace) →
                    roseLobeOsin_RegionAt K

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_Statement

/-- **The reduction**: the residual gives the cell-bound region choice (same thresholds; the
shared-arc bound comes from `roseLobeOsinPiece_sharedArcBound_of`). -/
theorem roseLobeOsinPiece_core_of (h : roseLobeOsinPiece_Statement.{u, w, v}) :
    roseLobeOsinCore_Statement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu h1 h2 h3 h4 h5
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W X lo hi hB hlea =>
    hrho rho hrho' W X lo hi hB hlea (roseLobeOsinPiece_sharedArcBound_of hB hlea)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_core_of

/-- **Equivalence certificate**: the cell-bound region choice gives the residual (drop the
shared-arc premise).  So the residual is logically equivalent to it, not weaker. -/
theorem roseLobeOsinPiece_of_core (h : roseLobeOsinCore_Statement.{u, w, v}) :
    roseLobeOsinPiece_Statement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu h1 h2 h3 h4 h5
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W X lo hi hB hlea _ => hrho rho hrho' W X lo hi hB hlea⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_of_core

/-- **The rose step from the residual.** -/
theorem roseLobeOsinPiece_rose_of (h : roseLobeOsinPiece_Statement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  roseLobeOsinCore_rose_of (roseLobeOsinPiece_core_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_rose_of

/-- **The outer-pinch step from the residual.** -/
theorem roseLobeOsinPiece_pinch_of (h : roseLobeOsinPiece_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeOsinCore_pinch_of (roseLobeOsinPiece_core_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_pinch_of

/-- **The Greendlinger leaf from the residual.** -/
theorem roseLobeOsinPiece_green_of (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeOsinPiece_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeOsinCore_green_of hoff (roseLobeOsinPiece_core_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_green_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
