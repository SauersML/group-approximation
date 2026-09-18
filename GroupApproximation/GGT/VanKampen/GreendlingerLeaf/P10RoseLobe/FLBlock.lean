import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.FLLists
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.FilterListing
import GroupApproximation.Meta.AxiomGuard

/-!
# The filtered lobe listing from one removed block

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-53.

`roseLobe_FilterListingStatement` (gl-p10-50) asks for a lobe `rs` such that, with
`P = movePred (lobeColour rs)`, (b) the kept darts of `K.sourceArc⁻¹` are `t₁⁻¹` for a cyclic
arc `t₁` of the source cell, (c) the kept darts of `K.targetArc` are a cyclic arc `t₂` of `∂X`
inside the old window, and (d) the kept darts of the boundary cycle form a closed dart walk.

The residual here, `roseLobeFL_BlockStatement`, drops every `CyclicArc` from the conclusion:
(b) becomes "the kept darts of `K.sourceArc⁻¹` form an infix of it"; (c) becomes "the kept darts
of `K.targetArc` form a prefix of a tail of it that does not wrap"; and (d) is replaced by
**the block clause**: the boundary cycle is `A ++ B ++ C` where either `P` removes all of `B`
(empty or a closed dart walk) and keeps all of `A ++ C ≠ []`, or `P` keeps all of the closed
dart walk `B` and removes all of `A ++ C`.  In words: the removed darts are one cyclically
contiguous block, and that block (equivalently, the kept part) closes up.

The reduction `roseLobeFL_filterListing_of_block` proves (b) and (c) from the infix and prefix
forms by the rotation arithmetic of `CyclicArc` (`FLLists`), and (d) from the block clause by
excising a closed sub-walk (`roseLobeFL_isClosedDartWalk_excise`).

## LOUD: strength of the residual

`roseLobeFL_BlockStatement` is **logically STRONGER** than `roseLobe_FilterListingStatement`,
not weaker: its infix and prefix clauses are equivalent to (b) and (c) (for (b), given the
properness bound and a duplicate-free cell boundary), but the block clause is strictly stronger
than (d), since a filtered closed walk can close up without the removed darts being one
contiguous block.  It is strictly smaller in proof
content: all the `CyclicArc` bookkeeping (start positions, wrap-around, windows) and the closing
of the filtered walk are proved here.  What stays open is pure planarity of the choice of lobe:
the kept darts of each of the two arcs are contiguous, and the removed darts form one closed
contiguous block of the cycle.

## Truth check (Python, `scratchpad/gl-p10-53/blk.py`, not formalised)

Built on the gl-p10-50 driver (`scratchpad/gl-p10-50/drive.py`).  For every configuration and
every admissible colouring `z` it checks the block clause with the stricter placement "kept
darts of `t₂` a PREFIX of `t₂`" (`k = 0`), and also (d) and the old statement.
* gl-p10-48 models: `315/315` configurations, block statement holds on all.
* Random planar maps, seeds 0 to 6:
  `32062 + 5614 + 25140 + 6734 + 3528 + 13736 + 14690 = 101504` configurations, `0` failures;
  `0` cases where the old statement holds and the block statement fails.
* The wrap-around disjunct is needed: a linear removed block alone fails on `1743` of them.
* The placement clauses are needed: on seed 7 (`2975` configurations) closed removed blocks
  that violate the placement exist in `315`, though a good block always exists.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

/-- **The lobe step with one removed block** (OPEN, PLAUSIBLE; truth-checked, see the module
docstring; LOUD: logically STRONGER than `roseLobe_FilterListingStatement`, with smaller proof
content).  Under the rose hypotheses there are roots `rs` as in the lobe statement such that, with
`P = movePred (lobeColour rs)`, the source cell of `K` stays outside and the kept cell of `K`
stays inside the flipped face set, the kept darts of `K.sourceArc⁻¹` are an infix of it, the
kept darts of `K.targetArc` are a prefix of its tail after `k` darts for some `k` with
`K.targetArc.start + k ≤ |∂X|`, and the boundary cycle is `A ++ B ++ C` where either `P` removes
all of `B` (empty or a closed dart walk) and keeps all of `A ++ C ≠ []`, or `P` keeps all of the
closed dart walk `B` and removes all of `A ++ C`. -/
def roseLobeFL_BlockStatement : Prop :=
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
          (cell X K.source).face ∉ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
            X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
          (cell X K.kept).face ∈ flipFaces X.toCombMap K.faces (roseJunctionCore_lobeColour
            X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) rs) ∧
          (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap
              (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
                rs)) <:+: invDarts X K.sourceArc.darts ∧
          (∃ k, K.targetArc.start.1 + k ≤ (outerDarts X).length ∧
            K.targetArc.darts.filter (movePred X.toCombMap
              (roseJunctionCore_lobeColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
                rs)) <+: K.targetArc.darts.drop k) ∧
          ∃ A B C : List X.toCombMap.Dart, K.boundary.cycle = A ++ B ++ C ∧
            ((B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
                (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = A ++ C ∧
                A ++ C ≠ [] ∧ (B = [] ∨ IsClosedDartWalk X.toCombMap B)) ∨
              (B.filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = B ∧
                (A ++ C).filter (movePred X.toCombMap (roseJunctionCore_lobeColour X.toCombMap
                  (walkKeep X.toCombMap K.boundary.cycle) rs)) = [] ∧
                IsClosedDartWalk X.toCombMap B))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_BlockStatement

/-- **The listing in the order of the cycle from one removed block.**  The arc `t₁` comes from
the infix of `K.sourceArc⁻¹`, the arc `t₂` from the prefix of the tail of `K.targetArc`, and the
filtered cycle closes up by excising the removed block. -/
theorem roseLobeFL_filterListing_of_block (h : roseLobeFL_BlockStatement.{u, w, v}) :
    roseLobe_FilterListingStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨rs, hroot, hsource, hkept, hb, ⟨k, hk, hc⟩, A, B, C, hABC, hblk⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨t₁, ht₁⟩ := roseLobeFL_exists_arc_invDarts_of_infix X K.sourceArc hb
  obtain ⟨t₂, ht₂, hst, hend⟩ := roseLobeFL_exists_arc_of_prefix_drop K.targetArc hk hc
  have hw : IsClosedDartWalk X.toCombMap K.boundary.cycle :=
    ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  exact ⟨rs, hroot, hsource, hkept, ⟨t₁, ht₁⟩, ⟨t₂, ht₂.symm, hst, hend⟩,
    roseLobeFL_isClosedDartWalk_filter_of_block hw hABC hblk⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_filterListing_of_block

/-- **The lobe removal from one removed block.** -/
theorem roseLobeFL_lobeRemoval_of_block (h : roseLobeFL_BlockStatement.{u, w, v}) :
    roseJunctionCore_LobeRemovalStatement.{u, w, v} :=
  roseLobe_lobeRemoval_of_filterListing (roseLobeFL_filterListing_of_block h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_lobeRemoval_of_block

/-- **The Greendlinger leaf from one removed block.** -/
theorem roseLobeFL_relativeGreendlinger_of_block
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : roseLobeFL_BlockStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  roseLobe_relativeGreendlinger_of_filterListing hoff (roseLobeFL_filterListing_of_block h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_relativeGreendlinger_of_block

/-- **The outer-pinch step from one removed block.** -/
theorem roseLobeFL_outerPinchStep_of_block (h : roseLobeFL_BlockStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  roseLobe_outerPinchStep_of_filterListing (roseLobeFL_filterListing_of_block h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeFL_outerPinchStep_of_block

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
