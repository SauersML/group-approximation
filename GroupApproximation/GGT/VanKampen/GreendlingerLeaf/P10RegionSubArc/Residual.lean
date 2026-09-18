import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.FilterMove
import GroupApproximation.Meta.AxiomGuard

/-!
# The sub-arc region move off the in-order case

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-87.

Target: `P10Rose.RoseRegionMoveSubArcStatement` (`P10Rose/Live/Reduction`).  Route:

1. For a pocket face set `K` with a proper source arc and a proper target arc, an in-order
   filter move `subArc_FilterMove K z` for any colouring `z` proves the goal of `K`
   (`subArc_goal_of_filterMove`, module `FilterMove`).
2. The residual `subArc_NoFilterMoveStatement` is the target restricted to the pocket face sets
   with **no** in-order filter move (the extra hypothesis `∀ z, ¬subArc_FilterMove K z`).
3. `regionMoveSubArc_of_noFilterMove`: split on whether some `z` is an in-order filter move.

## LOUD: strength of the residual

`subArc_NoFilterMoveStatement` is **implied by the target** (`noFilterMove_of_regionMoveSubArc`,
one line: forget the extra hypothesis), so it is true whenever the target is.  With the
reduction proved here, the two are therefore interchangeable as propositions; the gain is **proof
content**.  The residual only has to be proved for configurations where *no* colouring at all
(not only a lobe colouring) has its kept darts listed in the order of the cycle with the kept
parts of the two arcs as arcs and a closed kept walk.  Every configuration with a closed removed
block placed as in `subArc_filterMove_of_block` is discharged, which includes the one- and
two-dart lobes and lakes of `P10RoseLobe.MultiStatement` and every lobe witness of
`P10RoseLobe.roseLobe_FilterListingStatement`.  It is not an equivalent restatement of any FALSE
statement of the AVOID list: it asks for nothing beyond the target's own conclusion.

## Truth check (not formalised)

* The target is presumed TRUE: no refutation is known.  On the 24-dart model
  `P10RoseJunctionRefute.roseJunctionRefute_pK`, the gl-p10-87 search
  (`scratchpad/gl-p10-87/brute.py`) finds 210 witnesses of the target conclusion.  The same
  model has closed removed blocks (`scratchpad/gl-p10-87/run.py`): the one-dart region `{3}` and
  the region pairs `{2, 3}`, `{4, 5}` each remove one cyclically contiguous closed block.
* gl-p10-50 (`scratchpad/gl-p10-50/drive.py`): on `229556` random configurations, and on every
  gl-p10-48 model, a lobe colouring satisfies `roseLobe_FilterListingStatement`, whose
  conclusion gives an in-order filter move.  So on every tested configuration the extra
  hypothesis of the residual FAILS and the residual holds vacuously; what remains open is
  exactly the configurations (none known) in which no colouring is an in-order filter move.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove

/-- **The sub-arc region move off the in-order case** (OPEN; implied by the target, see the
module docstring).  The hypotheses of `P10Rose.RoseRegionMoveSubArcStatement`, together with the
hypothesis that no colouring is an in-order filter move, give the conclusion of the target. -/
def subArc_NoFilterMoveStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
      (∀ z : X.toCombMap.Dart → Bool, ¬subArc_FilterMove K z) →
        subArc_Goal K

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_NoFilterMoveStatement

/-- **The sub-arc region move from the residual.**  Either some colouring is an in-order filter
move, which proves the goal (`subArc_goal_of_filterMove`), or none is, and the residual applies. -/
theorem regionMoveSubArc_of_noFilterMove (h : subArc_NoFilterMoveStatement.{u, w, v}) :
    P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  have hgoal : subArc_Goal K := by
    rcases Classical.em (∃ z : X.toCombMap.Dart → Bool, subArc_FilterMove K z) with hm | hm
    · obtain ⟨z, hz⟩ := hm
      exact subArc_goal_of_filterMove K hsrc htgt hz
    · exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
        (fun z hz => hm ⟨z, hz⟩)
  unfold subArc_Goal at hgoal
  exact hgoal

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.regionMoveSubArc_of_noFilterMove

/-- **The residual is implied by the target**: forget the hypothesis on filter moves. -/
theorem noFilterMove_of_regionMoveSubArc (h : P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    subArc_NoFilterMoveStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose _
  unfold subArc_Goal
  exact h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.noFilterMove_of_regionMoveSubArc

/-- **The rose step from the residual**, through `P10Rose.rose_of_regionMoveSubArc`. -/
theorem subArc_rose_of_noFilterMove (h : subArc_NoFilterMoveStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  P10Rose.rose_of_regionMoveSubArc (regionMoveSubArc_of_noFilterMove h)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc.subArc_rose_of_noFilterMove

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionSubArc
