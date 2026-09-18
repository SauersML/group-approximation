import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.PlaceSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The lobe step with the automatic placement cases discharged

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-56.

`roseLobeBlk_BlockStatement` (gl-p10-54) asks for a lobe colouring
`z = roseJunctionCore_lobeColour M (walkKeep M c) rs` with the root clause, the source clause, the
kept clause, the two placement clauses (b'') and (c'') and one contiguous removed block
`c = A ++ B ++ C`.  The residual here, `roseLobePlace_Statement`, keeps the root clause and the
block clause and lets each other clause be replaced by a cheaper alternative:

* the source clause by *inner lobe* (every root has its face in the face set);
* the kept clause by *lake* (a single root with face outside the face set);
* both placement clauses by *lake*;
* placement (b'') by *non-bubble*: some dart of `B` is off the reversed source arc;
* placement (c'') by *non-bubble and no wrap*: some dart of `B` is off the target arc, and the
  target arc ends before the end of `outerDarts X`.

`roseLobePlace_blk_of_place` proves each alternative implies the clause it replaces
(`PlaceSides`), using only that `z` is a union of face classes and the list lemma
`roseLobePlace_filter_infix` (`PlaceLists`).

## LOUD: strength of the residual

`roseLobePlace_Statement` is **only EQUIVALENT** to `roseLobeBlk_BlockStatement` as a closed
proposition: both directions are proved (`roseLobePlace_blk_of_place`,
`roseLobePlace_place_of_blk`).  It is weaker pointwise (for fixed `rs`, `A`, `B`, `C` its
conclusion is implied by, and in general strictly weaker than, the old one), and strictly smaller
in proof content: the source clause for inner lobes, the kept clause and both placements for
lakes, and both placements for every non-bubble block are proved here.

It is NOT implied by contiguity alone.  The Python model `scratchpad/gl-p10-56/place.py` found
that of `1575` contiguous candidate colourings satisfying the root, source and kept clauses, `472`
fail placement; all of them are *bubbles*, whose removed block `B` lies strictly inside the
reversed source arc or strictly inside the target arc.  There were `0` failures for lakes, and a
placement-satisfying witness existed in every model.  So what stays open is: the existence of a
lobe with contiguous removed block, which is not a bubble unless it is a lake.  This is the
planar core (the choice of an extremal lobe) and is untouched here.

## Truth check (Python, not formalised)

Implied by `roseLobeBlk_BlockStatement` for the same witness (`roseLobePlace_place_of_blk`), so
the gl-p10-53 / gl-p10-54 checks (`101504` random configurations and `315` models, `0` failures)
carry over.  `scratchpad/gl-p10-56/lists.py` brute-forces `roseLobePlace_filter_infix` on all
splittings of short lists with constant pieces (`138849` cases, `0` failures).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The lobe step with the automatic placement cases discharged** (OPEN, PLAUSIBLE;
truth-checked, see the module docstring; LOUD: only EQUIVALENT to `roseLobeBlk_BlockStatement`,
with smaller proof content).  As `roseLobeBlk_BlockStatement`, except that the source clause may
be replaced by "every root face is in the face set", the kept clause by "a single root with face
outside the face set" (a lake), and the two placement clauses by "a lake", or each by the
existence of a dart of `B` off the arc (plus no wrap for the target arc). -/
def roseLobePlace_Statement : Prop :=
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
              (((invDarts X K.sourceArc.darts).filter (movePred X.toCombMap
                  (roseJunctionCore_lobeColour X.toCombMap
                    (walkKeep X.toCombMap K.boundary.cycle) rs)) <:+:
                  invDarts X K.sourceArc.darts ∨
                ∃ d ∈ B, d ∉ invDarts X K.sourceArc.darts) ∧
              ((∃ k, K.targetArc.start.1 + k ≤ (outerDarts X).length ∧
                  K.targetArc.darts.filter (movePred X.toCombMap
                    (roseJunctionCore_lobeColour X.toCombMap
                      (walkKeep X.toCombMap K.boundary.cycle) rs)) <+:
                    K.targetArc.darts.drop k) ∨
                (K.targetArc.start.1 + K.targetArc.length ≤ (outerDarts X).length ∧
                  ∃ d ∈ B, d ∉ K.targetArc.darts))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_Statement
