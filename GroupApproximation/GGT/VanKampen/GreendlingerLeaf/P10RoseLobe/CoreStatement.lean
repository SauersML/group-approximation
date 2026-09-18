import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.NoBubStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.CoreFacts
import GroupApproximation.Meta.AxiomGuard

/-!
# The no-bubble lobe step over the planar walk map

Lane gl-p10-60.  Notation: `M = X.toCombMap`, `c = K.boundary.cycle`,
`R = FaceClassStep M (walkKeep M c)` and `Γ = walkMap M c` (the map on the edges of the walk).

`roseLobeCore_Statement` is `roseLobeNoBub_Statement` (gl-p10-58) with its conclusion verbatim
and four more hypotheses, the planar picture of the regions cut out by the walk:

* `Γ` is planar (connected, Euler characteristic `2`);
* Jordan separation: darts of `Γ` are `R`-equivalent iff they lie on one face of `Γ`;
* cover: every `R`-class holds a dart of `Γ`;
* side constancy: `faceOf x ∈ K.faces` is constant on `R`-classes.

All four are proved in `CoreFacts` from `X.planar` alone (`roseLobeCore_planar`,
`roseLobeCore_iff`, `roseLobeCore_cover`, `roseLobeCore_side`), so `roseLobeCore_noBub_of`
discharges them, and `roseLobeCore_place_of`, `_blk_of`, `_lobeRm_of`, `_green_of` (with
`P07InnerPocket.PocketFourPieceOffStatement`) and `_pinch_of` follow through the `roseLobeNoBub_*`
reductions.

## LOUD: strength of the residual

`roseLobeCore_Statement` is **pointwise WEAKER** than `roseLobeNoBub_Statement` (same conclusion,
more hypotheses), but as a closed proposition it is **only EQUIVALENT** to it: both directions are
proved (`roseLobeCore_noBub_of`, `roseLobeCore_of_noBub`), since the added hypotheses are
theorems.  It is **NOT a strictly weaker true statement**.  None was found off the forbidden
routes: every weakening of the conclusion tried by gl-p10-58 (`forms.py`, V1-V6) is FALSE on the
generator, and a weaker true positional form has to be at least as strong as Place, which NoBub
already strengthens.  What this module removes is proof content only: the Jordan separation of the
sphere by the walk, the Euler count of `Γ`, the cover and the side constancy of the regions are
supplied, so a proof of the residual may reason about the faces of the planar map `Γ` directly.

## Remaining gap (the planar core)

Under the rose hypotheses, choose a set of faces of `Γ` (the regions of `c`), inside or outside
`K.faces` as the side hypothesis fixes, whose colouring meets the root, source and kept clauses
and removes one contiguous block `B` of `c = A ++ B ++ C`, which is a lake or sits on the two arcs
as in `roseLobeNoBub_Statement`.  Not proved here.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-60/core.py`, on the gl-p10-50 / gl-p10-54 / gl-p10-58 generator (the model of
gl-p10-58).  For every configuration it tests the ambient map planar, `Γ` (rotation: first return
of `σ`) connected with `V - E + F = 2`, separation on all pairs of walk darts, cover, and side
constancy.  Models: `315` configurations, `0` failures.  Random seeds `0`-`7` (`300` each):
`494752` configurations, `0` failures of any of the five checks.  With `--nobub` it reruns
gl-p10-58's check of the unchanged conclusion: models `1478` witnesses, seeds `0` and `5`
(`89290` and `49448` configurations; `214941` and `79784` witnesses), `0` without a witness.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The no-bubble lobe step over the planar walk map** (OPEN, PLAUSIBLE; truth-checked, see the
module docstring; LOUD: pointwise weaker than `roseLobeNoBub_Statement`, but EQUIVALENT to it as a
closed proposition).  As `roseLobeNoBub_Statement`, with the planarity, Jordan separation, cover
and side constancy of the walk map `Γ` as extra hypotheses. -/
def roseLobeCore_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
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
      (∀ x : X.toCombMap.Dart, ∃ y, walkKeep X.toCombMap K.boundary.cycle y ∧ Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) x y) →
      (∀ x y : X.toCombMap.Dart, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
          (walkKeep X.toCombMap K.boundary.cycle)) x y →
        (X.toCombMap.faceOf x ∈ K.faces ↔ X.toCombMap.faceOf y ∈ K.faces)) →
        ∃ rs : List X.toCombMap.Dart,
          ((rs ≠ [] ∧ ∀ r ∈ rs, r ∈ K.boundary.cycle) ∨
            ∃ r, rs = [r] ∧
              (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
                (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
              ∃ y ∈ K.boundary.cycle, Relation.EqvGen
                (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r y ∨
                Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha y)) ∧
          ((∀ r ∈ rs, X.toCombMap.faceOf r ∈ K.faces) ∨
            (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
              X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) ∧
          ((∃ r, rs = [r] ∧ X.toCombMap.faceOf r ∉ K.faces) ∨
            (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
              X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) ∧
          ∃ A B C : List X.toCombMap.Dart, K.boundary.cycle = A ++ B ++ C ∧
            ((B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
                (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = A ++ C ∧
                A ++ C ≠ []) ∨
              (B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = B ∧
                (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
                B ≠ [])) ∧
            ((∃ r, rs = [r] ∧ X.toCombMap.faceOf r ∉ K.faces) ∨
              (((A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                    (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∨
                  (∃ d ∈ B, d ∉ invDarts X K.sourceArc.darts) ∨
                  B <+: invDarts X K.sourceArc.darts ∨ B <:+ invDarts X K.sourceArc.darts) ∧
                ((∀ d ∈ B, d ∉ K.targetArc.darts) ∨
                  (C = [] ∧ B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour
                    X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) = []) ∨
                  ((A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour
                      X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
                    ∀ d ∈ A, d ∉ K.targetArc.darts))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_Statement

/-- **The no-bubble statement from the planar residual**: the four planar hypotheses are the
theorems of `CoreFacts`. -/
theorem roseLobeCore_noBub_of (h : roseLobeCore_Statement.{u, w, v}) :
    roseLobeNoBub_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose (roseLobeCore_planar K hK)
    (roseLobeCore_iff K hK) (roseLobeCore_cover K) (fun _ _ hxy => roseLobeCore_side K hxy)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_noBub_of

/-- **The planar residual from the no-bubble statement** (the converse: LOUD, the two are
equivalent). -/
theorem roseLobeCore_of_noBub (h : roseLobeNoBub_Statement.{u, w, v}) :
    roseLobeCore_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose _ _ _ _
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_of_noBub

/-- **Place from the planar residual.** -/
theorem roseLobeCore_place_of (h : roseLobeCore_Statement.{u, w, v}) :
    roseLobePlace_Statement.{u, w, v} :=
  roseLobeNoBub_place_of (roseLobeCore_noBub_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_place_of

/-- **The block statement from the planar residual.** -/
theorem roseLobeCore_blk_of (h : roseLobeCore_Statement.{u, w, v}) :
    roseLobeBlk_BlockStatement.{u, w, v} :=
  roseLobeNoBub_blk_of (roseLobeCore_noBub_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_blk_of

/-- **The lobe removal from the planar residual.** -/
theorem roseLobeCore_lobeRm_of (h : roseLobeCore_Statement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} :=
  roseLobeNoBub_lobeRm_of (roseLobeCore_noBub_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_lobeRm_of

/-- **The Greendlinger leaf from the planar residual.** -/
theorem roseLobeCore_green_of
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeCore_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeNoBub_green_of hoff (roseLobeCore_noBub_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_green_of

/-- **The outer-pinch step from the planar residual.** -/
theorem roseLobeCore_pinch_of (h : roseLobeCore_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeNoBub_pinch_of (roseLobeCore_noBub_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeCore_pinch_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
