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

/-- **The block statement from the cheaper alternatives.**  An inner lobe never flips the source
cell in, a lake never flips the kept cell out and removes no dart of either arc, and a
contiguous removed block with a dart off an arc filters that arc to an infix. -/
theorem roseLobePlace_blk_of_place (h : roseLobePlace_Statement.{u, w, v}) :
    roseLobeBlk_BlockStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨rs, hroot, hsw, hkw, A, B, C, hABC, hblk, hpos⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hs := roseLobePlace_src_of K hsw
  refine ⟨rs, hroot, hs, roseLobePlace_kept_of K hkw, ?_, ?_, A, B, C, hABC, hblk⟩
  · rcases hpos with ⟨r, hrs, hr⟩ | ⟨h1, -⟩
    · exact roseLobePlace_place1_of_side K
        (roseJunctionCore_lobeColour_step X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs)
        (fun d hd => roseLobePlace_lake_eq_false K.boundary.cycle_mem_iff hrs hr hd) hs
    · rcases h1 with h1 | h1
      · exact h1
      · exact roseLobePlace_place1_of_esc K hABC hblk h1
  · rcases hpos with ⟨r, hrs, hr⟩ | ⟨-, h2⟩
    · exact roseLobePlace_place2_of_side K
        (fun d hd => roseLobePlace_lake_eq_false K.boundary.cycle_mem_iff hrs hr hd)
        (fun d hd => roseLobePlace_lake_outer K hrs hr hroot hd)
    · rcases h2 with h2 | ⟨hnw, h2⟩
      · exact h2
      · exact roseLobePlace_place2_of_esc K hABC hblk hnw h2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_blk_of_place

/-- **The converse**: the block statement gives the residual with every alternative taken on the
old side, so the two are equivalent as closed propositions. -/
theorem roseLobePlace_place_of_blk (h : roseLobeBlk_BlockStatement.{u, w, v}) :
    roseLobePlace_Statement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨rs, hroot, hs, hk, hb, hcc, A, B, C, hABC, hblk⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨rs, hroot, Or.inr hs, Or.inr hk, A, B, C, hABC, hblk,
    Or.inr ⟨Or.inl hb, Or.inl hcc⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_place_of_blk

/-- **The filtered lobe listing from the residual.** -/
theorem roseLobePlace_filterListing_of_place (h : roseLobePlace_Statement.{u, w, v}) :
    roseLobe_FilterListingStatement.{u, w, v} :=
  roseLobeBlk_filterListing_of_weak (roseLobePlace_blk_of_place h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_filterListing_of_place

/-- **The lobe removal from the residual.** -/
theorem roseLobePlace_lobeRemoval_of_place (h : roseLobePlace_Statement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} :=
  roseLobeBlk_lobeRemoval_of_weak (roseLobePlace_blk_of_place h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_lobeRemoval_of_place

/-- **The Greendlinger leaf from the residual.** -/
theorem roseLobePlace_relativeGreendlinger_of_place
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobePlace_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobeBlk_relativeGreendlinger_of_weak hoff (roseLobePlace_blk_of_place h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_relativeGreendlinger_of_place

/-- **The outer-pinch step from the residual.** -/
theorem roseLobePlace_outerPinchStep_of_place (h : roseLobePlace_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobeBlk_outerPinchStep_of_weak (roseLobePlace_blk_of_place h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobePlace_outerPinchStep_of_place

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
