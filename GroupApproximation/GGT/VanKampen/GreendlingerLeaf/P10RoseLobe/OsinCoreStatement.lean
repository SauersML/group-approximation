import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinCoreBounds
import GroupApproximation.Meta.AxiomGuard

/-!
# The region choice from the cell bounds of Osin's condition

Lane gl-p10-76.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

`roseLobeOsinCore_Statement` is `roseLobeOsin_RegionStatement` with the family condition
`OsinCCondition D W ε μ λ c ρ` replaced by the cell bounds `roseLobeOsinCore_CellBounds D W X ε μ
λ c ρ` on the diagram (module `OsinCoreBounds`).  The cell bounds are inverse and rotation
closure, long, qg on relator cells, and pieces.  Hyperbolicity and the thresholds
`0 < λ ≤ 1`, `0 ≤ c`, `0 < μ ≤ 1/16`, `ε₀`, `ρ₀` are kept.  It drops `admissible`, `deep`,
`publishedPiecesSmall`, and the qg clause for words of `W` that label no cell of `X`.

## Proof of the reduction

`roseLobeOsinCore_region_of`: given the thresholds `ε₀`, `ρ₀` of the core statement, use the
same thresholds for `roseLobeOsin_RegionStatement`.  At `OsinCCondition` hypothesis `hC` and
diagram `X`, `roseLobeOsinCore_cellBounds_of hC X` supplies the cell bounds, and every other
premise is passed through unchanged.

`roseLobeOsinCore_of_region`: the (FALSE) `roseLobeRegion_Statement` implies the core
statement at `ε₀ = 0`, `ρ₀ = 1`, because it has none of the extra premises.  So the core statement
is no stronger than the unrepaired chain.

## Truth check (LOUD)

Scripts `long_audit.py` and `qg_audit.py` are in the lane scratchpad.  The family is the gl-p10-72
counterexample family: the 16-dart map with faces
`[0,15,4] [1,14] [2,6,10,11] [3] [5,9] [7,12] [8,13]` and its 1260 failing configurations.
Relator-cell lengths are made long by weighted subdivision (so a monogon is NOT excluded for
free).  The limit is `ε → ∞`, `ρ / ε → ∞`, which is allowed because `ρ₀` is chosen after `ε`.

* **long only**: 84 of 1260 survive.
* **LOUD: long + pieces is NOT enough.**  42 survive.  In each the kept cell is
  `K0 = [2,6,10,11]`, whose only off-side edge is the spike `{10, 11}`.  Subdivided with weights,
  they still fail the Region conclusion.
* **LOUD: long + qg is NOT enough.**  42 survive.  In each the source cell `S` is the 2-gon
  `[1,14]`, and every edge of `S` is shared with `K0 = [0,15,4]`.
* **long + qg + pieces**: all 1260 are killed.  The model has every non-relator face a G-cell,
  and optionally one extra relator cell.
  * qg kills the spike.  A spike reads `[ℓ d, (ℓ d)⁻¹]`, of value `1`, so `2 λ ≤ c`
    (`roseLobeOsinCore_two_mul_le_of_spike`), and every value-one arc has at most `c / λ`
    darts, which is bounded while `ρ → ∞`.
  * pieces kills the shared 2-gon: its whole boundary is a union of direct pieces, so
    `|S| < k μ |S|` with `k μ ≤ 1`.
* Random configurations: seeds 8, 12, 13, 14, 16, 17, 18, 21, 22 and 23 ran 0.42–1.03 M
  configurations each with 0 Region failures.  Seed 5 had 1260 failures, all of them this
  family.  Some seeds were still running at report time.
* NOT modelled:
  * least area;
  * pieces through nontrivial connectors, that is, the general piece LP;
  * the genericity clause `listVal v' ≠ y · listVal v · y⁻¹` of `IsPiece`.  A shared arc is a
    piece only if the two cells are not a cancellable pair, and excluding such pairs needs a
    least-area surgery that is not proved here;
  * a non-free `G`.

## Remaining gap

`roseLobeOsinCore_Statement` itself (OPEN, not refuted).  In particular:

1. the cancellable-pair exclusion from `X.LeastArea`, so that shared arcs are pieces;
2. the general piece / length count over the pocket.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The region choice from the cell bounds** (OPEN, not refuted; see the module docstring).
`roseLobeOsin_RegionStatement` with `OsinCCondition D W ε μ λ c ρ` replaced by the cell bounds
`roseLobeOsinCore_CellBounds D W X ε μ λ c ρ` of the diagram `X`. -/
def roseLobeOsinCore_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
            roseLobeOsinCore_CellBounds D W X eps mu lambda c rho → X.LeastArea →
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
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_Statement

/-- **The reduction**: the cell-bound region choice gives the Osin one (same thresholds; the
cell bounds come from `roseLobeOsinCore_cellBounds_of`). -/
theorem roseLobeOsinCore_region_of (h : roseLobeOsinCore_Statement.{u, w, v}) :
    roseLobeOsin_RegionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu h1 h2 h3 h4 h5
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hC X lo hi =>
    hrho rho hrho' W X lo hi (roseLobeOsinCore_cellBounds_of hC X)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_region_of

/-- **Truth certificate**: the (FALSE) unrepaired region choice implies the cell-bound one
(`ε₀ = 0`, `ρ₀ = 1`), so the new residual is no stronger than it. -/
theorem roseLobeOsinCore_of_region (h : roseLobeRegion_Statement.{u, w, v}) :
    roseLobeOsinCore_Statement.{u, w, v} := by
  intro G _ Lambda D _ _ _ _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ _ X lo hi _ hlea hlabel K hK hnft hsrc
    htgt hpinch hrose hpl hiff hcov hside hI hT => h D eps X lo hi hlea hlabel K hK hnft hsrc
      htgt hpinch hrose hpl hiff hcov hside hI hT⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_of_region

/-- **The rose step from the cell-bound region choice.** -/
theorem roseLobeOsinCore_rose_of (h : roseLobeOsinCore_Statement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  roseLobeOsin_rose_of (roseLobeOsinCore_region_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_rose_of

/-- **The outer-pinch step from the cell-bound region choice.** -/
theorem roseLobeOsinCore_pinch_of (h : roseLobeOsinCore_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeOsin_pinch_of (roseLobeOsinCore_region_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_pinch_of

/-- **The Greendlinger leaf from the cell-bound region choice.** -/
theorem roseLobeOsinCore_green_of (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeOsinCore_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeOsin_green_of hoff (roseLobeOsinCore_region_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_green_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
