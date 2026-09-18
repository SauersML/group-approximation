import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinSelfBound
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell-bound region choice with the all-pairs shared-arc bound supplied

Lane gl-p10-81.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The two statements

* `roseLobeOsinSelf_Statement` is `roseLobeOsinCore_Statement` with the premise
  `roseLobeOsinSelf_SharedArcBoundAll X μ` (module `OsinSelfBound`) inserted right after
  `X.LeastArea`.  This covers arcs a cell shares with itself as well.
* `roseLobeOsinSelf_NonGenStatement` is the residual of the self case.  It has the threshold
  shape of the core statement, `∃ ε₀, ∀ ε ≥ ε₀, ∃ ρ₀ > 0, ∀ ρ ≥ ρ₀`, and then, for every
  diagram `X` with the cell bounds, least area and letter labels, it gives
  `roseLobeOsinSelf_NonGenericBound X μ`.

## The reductions

* `roseLobeOsinSelf_core_of`: the two statements give the core statement.  Take
  `ε₀ = max ε₀' ε₀''` and then `ρ₀ = max ρ₀' ρ₀''`.  The all-pairs premise is supplied by
  `roseLobeOsinSelf_sharedArcBound`.
* `roseLobeOsinSelf_of_core`: the core statement gives `roseLobeOsinSelf_Statement`, by dropping
  the premise.
* `roseLobeOsinSelf_of_piece`: `roseLobeOsinPiece_Statement` gives it too, since the all-pairs
  bound implies the distinct-pairs one (`roseLobeOsinSelf_pairs_of_all`).

## Strength (LOUD)

* `roseLobeOsinSelf_Statement` is implied by both the core statement and the piece statement.
  It is equivalent to them only modulo the residual `roseLobeOsinSelf_NonGenStatement`.  It is
  **not** proved equivalent here.
* The residual is strictly smaller in proof content than the core statement.  It is a local
  statement about one relator cell of one diagram.  It has no pocket, no region choice and no
  planar pocket hypotheses.  It is needed only in the non-generic, self-shared case.
* **Truth of the residual** (OPEN, not refuted; scratchpad `gl-p10-81/self_arc.py`).
  1. Planarity.  In all 18596 connected planar maps with at most 4 edges, every edge whose two
     darts lie on one face is a bridge (28193 cases).  Every edge of every self-overlap arc is
     such an edge (108092 arcs).  So the cell reads cyclically `w X w⁻¹ Y`, and `X` bounds a
     sub-diagram `C₂` that holds no outer face.
  2. Free groups.  Here non-genericity forces the relator value to be `1` (no counterexample
     among 161² pairs of reduced words).  That is excluded by qg and long.
  3. Torsion.  In `D∞` non-genericity occurs with a relator value of infinite order.  So the
     residual is NOT a formal consequence of the genericity algebra.  Its expected proof is
     qg when `C₂` has no relator cell, and otherwise Greendlinger's lemma on the least-area
     sub-diagram `C₂` whose boundary is a qg arc of the cell.  That is an area induction
     inside the main theorem.
  4. The earlier long/qg/pieces audit (`OsinCoreStatement`, 1260 configurations) was not
     rerun with the self-overlap premise.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The non-generic self-overlap residual** (OPEN, not refuted; see the module docstring).
Beyond thresholds `ε₀`, `ρ₀`, every diagram with the cell bounds, least area and letter labels
has the non-generic self-overlap bound. -/
def roseLobeOsinSelf_NonGenStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W),
            roseLobeOsinCore_CellBounds D W X eps mu lambda c rho → X.LeastArea →
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                roseLobeOsinSelf_NonGenericBound X mu

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_NonGenStatement

/-- **The cell-bound region choice with the all-pairs shared-arc bound supplied** (OPEN, not
refuted; see the module docstring).  `roseLobeOsinCore_Statement` with the extra premise
`roseLobeOsinSelf_SharedArcBoundAll X μ` after `X.LeastArea`. -/
def roseLobeOsinSelf_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
            roseLobeOsinCore_CellBounds D W X eps mu lambda c rho → X.LeastArea →
              roseLobeOsinSelf_SharedArcBoundAll X mu →
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
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_Statement

/-- **The reduction**: the all-pairs region choice and the non-generic self-overlap residual
give the cell-bound region choice (thresholds: maxima of the two). -/
theorem roseLobeOsinSelf_core_of (hN : roseLobeOsinSelf_NonGenStatement.{u, w, v})
    (h : roseLobeOsinSelf_Statement.{u, w, v}) : roseLobeOsinCore_Statement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨e1, he1⟩ := h D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨e2, he2⟩ := hN D hhyp lambda c mu h1 h2 h3 h4 h5
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨r1, hr1, hs1⟩ := he1 eps (le_of_max_le_left heps)
  obtain ⟨r2, -, hs2⟩ := he2 eps (le_of_max_le_right heps)
  refine ⟨max r1 r2, lt_of_lt_of_le hr1 (le_max_left r1 r2), ?_⟩
  intro rho hrho W X lo hi hB hlea hlab
  exact hs1 rho (le_of_max_le_left hrho) W X lo hi hB hlea
    (roseLobeOsinSelf_sharedArcBound hB hlea
      (hs2 rho (le_of_max_le_right hrho) W X hB hlea hlab)) hlab

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_core_of

/-- **Certificate**: the cell-bound region choice gives the all-pairs one (drop the premise),
so `roseLobeOsinSelf_Statement` is no stronger than it. -/
theorem roseLobeOsinSelf_of_core (h : roseLobeOsinCore_Statement.{u, w, v}) :
    roseLobeOsinSelf_Statement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu h1 h2 h3 h4 h5
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W X lo hi hB hlea _ => hrho rho hrho' W X lo hi hB hlea⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_of_core

/-- **Certificate**: the distinct-pairs region choice gives the all-pairs one, so
`roseLobeOsinSelf_Statement` is no stronger than `roseLobeOsinPiece_Statement`. -/
theorem roseLobeOsinSelf_of_piece (h : roseLobeOsinPiece_Statement.{u, w, v}) :
    roseLobeOsinSelf_Statement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu h1 h2 h3 h4 h5
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W X lo hi hB hlea hall =>
    hrho rho hrho' W X lo hi hB hlea (roseLobeOsinSelf_pairs_of_all hall)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_of_piece

/-- **The rose step from the all-pairs region choice and the residual.** -/
theorem roseLobeOsinSelf_rose_of (hN : roseLobeOsinSelf_NonGenStatement.{u, w, v})
    (h : roseLobeOsinSelf_Statement.{u, w, v}) : P10ChordLift.RoseStepStatement.{u, w, v} :=
  roseLobeOsinCore_rose_of (roseLobeOsinSelf_core_of hN h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_rose_of

/-- **The outer-pinch step from the all-pairs region choice and the residual.** -/
theorem roseLobeOsinSelf_pinch_of (hN : roseLobeOsinSelf_NonGenStatement.{u, w, v})
    (h : roseLobeOsinSelf_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeOsinCore_pinch_of (roseLobeOsinSelf_core_of hN h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_pinch_of

/-- **The Greendlinger leaf from the all-pairs region choice and the residual.** -/
theorem roseLobeOsinSelf_green_of (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hN : roseLobeOsinSelf_NonGenStatement.{u, w, v})
    (h : roseLobeOsinSelf_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeOsinCore_green_of hoff (roseLobeOsinSelf_core_of hN h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinSelf_green_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
