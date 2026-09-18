import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.PlaceBlock
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.NoBubSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The lobe step as a positional no-bubble statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-58.

`roseLobePlace_Statement` (gl-p10-56) asks for a lobe colouring with the root, source, kept and
block clauses, and two *placement* clauses about the filtered arcs: the kept darts of the reversed
source arc `I = invDarts X K.sourceArc.darts` form an infix of `I`, and the kept darts of the target
arc `t2 = K.targetArc.darts` form a prefix of some drop `t2.drop k` with `start + k ≤ n`, unless
the lobe is a lake.  `roseLobeNoBub_Statement` keeps the root, source, kept and block clauses
verbatim and replaces both placement clauses by conditions on the *position* of the block
`c = A ++ B ++ C` alone (no filtered arc, no drop, no wrap bound):

* source side: `P` removes `A ++ C`, or some dart of `B` is off `I`, or `B` is a prefix or a
  suffix of `I`;
* target side: no dart of `B` is on `t2`, or `C = []` and `P` removes `B`, or `P` removes
  `A ++ C` and no dart of `A` is on `t2`.

This is "no bubble": the excluded rm-form blocks are exactly those strictly inside `I`, and the
excluded target cases are those where the kept part of `t2` does not start at the arc start.
`roseLobeNoBub_place_of` proves the reduction, through `roseLobeNoBub_place1` and
`roseLobeNoBub_place2` (`NoBubSides`, `NoBubLists`); the target placement always uses `k = 0`.

## LOUD: strength of the residual

`roseLobeNoBub_Statement` is **pointwise STRONGER** than `roseLobePlace_Statement`: for a fixed
witness `rs, A, B, C`, its conclusion implies Place's (proved), and not conversely.  On the source
side the two agree for a nodup cycle; on the target side Place also accepts, with a drop `k > 0`
and no wrap, an rm block that meets `t2` with `C ≠ []` (for example one covering the start of
`t2`), and a kp block with a dart of `A` on `t2` (for example strictly inside `t2`), which the
clause here rejects.  As a closed proposition it
implies `roseLobePlace_Statement`; **the converse is NOT proved** (it would need the planar core
below).  So this is NOT a weaker statement.  What it buys is strictly smaller proof content: the
filter, infix, drop and wrap analysis of both placements is discharged here, and what is left is
the positional existence claim alone.

## Remaining gap (the planar core)

Existence, under the rose hypotheses, of a lobe colouring with the root, source and kept clauses
and one contiguous removed block, which is a lake or sits on the cycle as above.  The
complement-lobe exchange does not give this: for a bubble lobe `Z` the kept clause forces
`K.kept ∉ Z`, so the complementary lobe flips the kept cell out.

## Truth check (Python, not formalised)

`scratchpad/gl-p10-58/nobub_lean.py` extends `gl-p10-56/place.py` on the gl-p10-50 / gl-p10-54
generator.  For every configuration it searches all lobe and lake colourings passing the source and
kept clauses and all splittings `cyc = A ++ B ++ C` in rm or kp form, and tests the clause exactly
as stated here.  Models: `315` configurations, `0` without a witness, `1478` witnesses.  Random
seeds `0`-`7` (`300` each): `494752` configurations, `0` without a witness.  Every non-lake witness
(`1111562` random, `1478` model) was also checked to satisfy Place's placement with `k = 0`
(`0` unsound).  Weaker positional forms FAIL: dropping the prefix/suffix-of-`I` alternative fails
on seeds `5` and `6` (`gl-p10-58/forms.py`, variants V1-V3, V5), and dropping the kp alternatives
fails on the models (V4, V6).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The lobe step as a positional no-bubble statement** (OPEN, PLAUSIBLE; truth-checked, see the
module docstring; LOUD: pointwise STRONGER than `roseLobePlace_Statement`, which it implies; the
converse is not proved).  As `roseLobePlace_Statement`, with both placement clauses replaced by
conditions on the position of the block `B` relative to the two arcs. -/
def roseLobeNoBub_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
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

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_Statement

/-- **Place from the no-bubble statement**: the positional source clause gives the infix
placement of the reversed source arc, and the positional target clause gives the prefix placement
of the target arc with `k = 0`. -/
theorem roseLobeNoBub_place_of (h : roseLobeNoBub_Statement.{u, w, v}) :
    roseLobePlace_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨rs, hroot, hsw, hkw, A, B, C, hABC, hblk, hpos⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  refine ⟨rs, hroot, hsw, hkw, A, B, C, hABC, hblk, ?_⟩
  rcases hpos with hlake | ⟨h1, h2⟩
  · exact Or.inl hlake
  · exact Or.inr ⟨Or.inl (roseLobeNoBub_place1 K hABC hblk h1),
      Or.inl (roseLobeNoBub_place2 K hABC hblk h2)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_place_of

/-- **The block statement from the no-bubble statement.** -/
theorem roseLobeNoBub_blk_of (h : roseLobeNoBub_Statement.{u, w, v}) :
    roseLobeBlk_BlockStatement.{u, w, v} :=
  roseLobePlace_blk_of_place (roseLobeNoBub_place_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_blk_of

/-- **The lobe removal from the no-bubble statement.** -/
theorem roseLobeNoBub_lobeRm_of (h : roseLobeNoBub_Statement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} :=
  roseLobePlace_lobeRemoval_of_place (roseLobeNoBub_place_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_lobeRm_of

/-- **The Greendlinger leaf from the no-bubble statement.** -/
theorem roseLobeNoBub_green_of
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeNoBub_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobePlace_relativeGreendlinger_of_place hoff (roseLobeNoBub_place_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_green_of

/-- **The outer-pinch step from the no-bubble statement.** -/
theorem roseLobeNoBub_pinch_of (h : roseLobeNoBub_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobePlace_outerPinchStep_of_place (roseLobeNoBub_place_of h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_pinch_of

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
