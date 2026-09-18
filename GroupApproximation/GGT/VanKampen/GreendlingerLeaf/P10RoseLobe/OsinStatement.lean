import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinPointLobe
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.Cases
import GroupApproximation.Meta.AxiomGuard

/-!
# The region choice under Osin's condition

Lane gl-p10-74.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## LOUD: `roseLobeCore_Statement` is FALSE (hence so is `roseLobeNoBub_Statement`)

Exhaustive check (script `core_audit.py`, 1260 of 1260 choices of `rs` fail): the 16-dart
diagram with faces `[0,15,4] [1,14] [2,6,10,11] [3] [5,9] [7,12] [8,13]`, boundary cycle
`c = [0,15,2,8,6,4,13]`, face set `F = {0, 2, 6}`, source cell `S = 3`, kept cell `0`, outer
face `1`, `t₁ = t₂ = []`, `s₁ = []` and `s₂ = c`.  It satisfies every hypothesis of
`roseLobeCore_Statement` and no `rs` satisfies its conclusion.  `roseLobeNoBub_Statement` has
the same conclusion and hypotheses, so it is FALSE too (the gl-p10-72 counterexample to
`roseLobeRegion_Statement`, `Choice`, `Multi` and `Triple` is the same diagram).

## Repair: the RoseStep premises

`roseLobeOsin_RegionStatement` is `roseLobeRegion_Statement` with the premises of
`P10ChordLift.RoseStepStatement` (hyperbolicity, `0 < λ ≤ 1`, `0 ≤ c`, `0 < μ ≤ 1/16`, the
thresholds `ε₀`, `ρ₀`, and `OsinCCondition D W ε μ λ c ρ`) put back.  Every reduction of the lobe
chain is pointwise, so the conclusion at `K` still reaches the rose step
(`roseLobeOsin_rose_of`, through `P10RoseLobe/OsinPoint`, `OsinPointLobe`), then
`roseLobeOsin_pinch_of` and `roseLobeOsin_green_of`.  `roseLobeOsin_region_of_region` shows the
residual is WEAKER than the (FALSE) `roseLobeRegion_Statement` (take `ε₀ = 0`, `ρ₀ = 1`).

## Truth check (LOUD: partial)

The source cell `S = 3` of the counterexample is a monogon.  `roseLobeOsin_rho_le_cell`: under
`OsinCCondition` every cell has at least `ρ` darts, so for `ρ ≥ 2` (`roseLobeOsin_one_lt_cell`)
the counterexample is excluded.  LOUD caveat: the `long` field alone is NOT a robust exclusion.
Subdividing every edge `m` times (script `subdiv_audit.py`, `m = 1, 2, 3, 5`) still fails the
Core conclusion and has cells of at least `m` darts, so `long` holds for `ρ ≤ m`.  A
real exclusion must use `pieces_small` (`μ ≤ 1/16`), the quasi-geodesic clause, least area or
hyperbolicity.  That is plausible, since `S` shares its whole boundary with face `2` (one piece
of length `|S|`, far above `μ |S|`), but it is not checked in Lean.

## Remaining gap

`roseLobeOsin_RegionStatement` itself (OPEN, not refuted).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The region choice under Osin's condition** (OPEN, not refuted; see the module docstring).
`roseLobeRegion_Statement` with the premises of `P10ChordLift.RoseStepStatement`. -/
def roseLobeOsin_RegionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
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
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_RegionStatement

/-- **Truth certificate**: the (FALSE) region choice implies the Osin one (`ε₀ = 0`, `ρ₀ = 1`),
so the new residual is weaker. -/
theorem roseLobeOsin_region_of_region (h : roseLobeRegion_Statement.{u, w, v}) :
    roseLobeOsin_RegionStatement.{u, w, v} := by
  intro G _ Lambda D _ _ _ _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ _ _ X lo hi hlea hlabel K hK hnft hsrc htgt
    hpinch hrose hpl hiff hcov hside hI hT => h D eps X lo hi hlea hlabel K hK hnft hsrc htgt
      hpinch hrose hpl hiff hcov hside hI hT⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_region_of_region

/-- Under `OsinCCondition` every relator cell has at least `ρ` darts. -/
theorem roseLobeOsin_rho_le_cell {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} (hC : OsinCCondition D W eps mu lambda c rho)
    (X : DiscDiagram.{u, w, v} W) (i : Fin X.rCellCount) : rho ≤ (cellDarts X i).length := by
  have hlength := congrArg List.length (dartWord_cellDarts X i)
  have hw := hC.long _ (cell X i).word_mem
  simp only [dartWord, List.length_map] at hlength
  omega

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_rho_le_cell

/-- **The counterexample violates `OsinCCondition`** once `2 ≤ ρ`: no relator cell is a
monogon, while the source cell `S = 3` of the 16-dart counterexample has one dart. -/
theorem roseLobeOsin_one_lt_cell {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} (hC : OsinCCondition D W eps mu lambda c rho) (h2 : 2 ≤ rho)
    (X : DiscDiagram.{u, w, v} W) (i : Fin X.rCellCount) : 1 < (cellDarts X i).length := by
  have := roseLobeOsin_rho_le_cell hC X i
  omega

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_one_lt_cell

/-- **The rose step from the Osin region choice.**  The thresholds are those of the residual;
the planar, cover, side and facing premises are proved (`roseLobeCore_planar`, ...,
`roseLobeRegion_faceOf_alpha_tgt`); the pointwise chain Region, Core, Blk, filtered listing,
lobe removal, sub-arc move, in-place step runs at `K`; the diagram is kept. -/
theorem roseLobeOsin_rose_of (h : roseLobeOsin_RegionStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu h1 h2 h3 h4 h5
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu h1 h2 h3 h4 h5
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho' W hC X lo hi hlea hlabel K hK hnft hsrc htgt hpinch
    hrose => ?_⟩
  have hreg := hrho rho hrho' W hC X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
    (roseLobeCore_planar K hK) (roseLobeCore_iff K hK) (roseLobeCore_cover K)
    (fun _ _ hxy => roseLobeCore_side K hxy) (fun d hd => roseLobeRegion_faceOf_alpha_inv K hd)
    (fun d hd => roseLobeRegion_faceOf_alpha_tgt K hd)
  obtain ⟨K', hK', hsrc', htgt', hlt⟩ := roseLobeOsin_inPlaceAt_of K hlabel hK
    (roseLobeOsin_subArcAt_of K (roseLobeOsin_lobeAt_of K hsrc htgt
      (roseLobeOsin_filterAt_of K hK (roseLobeOsin_blkAt_of K (roseLobeOsin_coreAt_of K hreg)))))
  exact ⟨X, K', ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hK', hsrc', htgt', hlt⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_rose_of

/-- **The outer-pinch step from the Osin region choice.** -/
theorem roseLobeOsin_pinch_of (h : roseLobeOsin_RegionStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  Piece10.proof_of_rose (roseLobeOsin_rose_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_pinch_of

/-- **The Greendlinger leaf from the Osin region choice**: the route of
`P10RoseExtremalTrim.roseJunctionCore_relativeGreendlinger_of_lobeRemoval` with the outer-pinch
step from `roseLobeOsin_pinch_of`. -/
theorem roseLobeOsin_green_of (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeOsin_RegionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow
    Piece01.proof.{u, w, v} Piece04.proof.{u, w, v}
    (P06Bypass.refutedBelowSection_of_innerPocketEnclosed
      (P07InnerPocket.innerPocketEnclosed_of_fourPieceOff hoff))
    (roseLobeOsin_pinch_of h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsin_green_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
