import GroupApproximation.Manuscript.NonMF.Full.GL06.Waist
import GroupApproximation.Manuscript.NonMF.Full.GL06.BinderFive
-- PROVISIONAL sibling endpoint modules (not on origin/main yet; names from fk/status/<lane>.md,
-- or proposed in GL06's work orders where the lane has not fixed one).
import GroupApproximation.Manuscript.NonMF.Full.GL06a.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06b.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06c.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06d.NonRose
import GroupApproximation.Manuscript.NonMF.Full.GL06e.Refuted
import GroupApproximation.Manuscript.NonMF.Full.GL06f.Reduction
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL03D.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06: Osin's Lemma 4.4 at least-area diagrams, unconditionally

The relative Greendlinger lemma at least-area diagrams:
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (module
`GGT.VanKampen.Estimating.OsinAppendixSections`). Source: Osin, arXiv:math/0411039v3, Lemma 4.4,
proved through Lemmas 9.4 and 9.7(b). This is the Greendlinger waist of Hull's small cancellation
theorem, `thm:hull` (non_mf_groups_exist.tex, around line 2121), used by the torsion-free results of
non_mf_groups_exist.tex. On its own it certifies no printed sentence.

Route: the Below waist with residuals as hypotheses,
`Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals` (`Full/GL06/Waist`), which
already supplies residual 04 (`Full.GL02.gapSpan`) and residual 08 (`P08ProperArc.proof`). The
remaining binders come from sibling lanes. Names marked PROVISIONAL are not landed yet.

* `hbudget` (residual 01): PROVISIONAL `Full.GL06a.budget`.
* `htwocopy` (residual 05): PROVISIONAL `Full.GL06b.twoGonCleanCopy`.
* `hwhole` (residual 09): PROVISIONAL `Full.GL06c.wholeSectionTwoArc`.
* `hcopy` (binder 5, residuals 06 and 07): `Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`
  (`Full/GL06/BinderFive`) applied to PROVISIONAL
  `Full.GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected :
    Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected →
    Full.GL06e.CellPocketWalkRefutedBelowSectionStatement`, applied to PROVISIONAL
  `Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected`.  The all-cells disjunct of the corrected
  statement is excluded inside that endpoint, through the refutation of lane GL06h (WO-GL06-7).
  The original `Full.GL03B.InnerPocketEnclosedTwoArcLocal` is false (GL03BPinch), so it is not
  consumed.
* `hstep` (residual 10): `Full.GL06.outerPinchStep_of_cases` of
  * PROVISIONAL `Full.GL06d.nonRoseStep`, whose type must be definitionally
    `Full.GL06.NonRoseStepStatement` (over `Full.GL06f.AllNonFirstTurnsCrossed`, not the
    non-compiling `P10ChordLift` predicate), and
  * the landed `Full.GL06f.rose_of_regionMoveSubArc` applied to PROVISIONAL
    `Full.GL03D.roseRegionMoveSubArc : Full.GL06f.RoseRegionMoveSubArcStatement`.

GL05c's counterexample (fk/orders/GL05c-counterexample.md) killed the rose junction route
(`P10RoseExtremalTrim.RoseExtremalJunctionStatement`, GL03C Endpoint). The rose step is consumed
only through the sub-arc region move.
-/

namespace GroupApproximation.Full.GL06

universe u w v

open GroupApproximation.GGT.VanKampen

/-- **Osin's Lemma 4.4 at least-area diagrams** (relative Greendlinger lemma; `thm:hull`
infrastructure, non_mf_groups_exist.tex ~2121). Take a hyperbolic relative generating set and
`0 < λ ≤ 1`, `0 ≤ c`, `0 < μ ≤ 1/16`. Then there are `ε` and `ρ > 0` with the following property.
Every least-area disc diagram over a `C(ε, μ, λ, c, ρ)` relator set whose boundary is
`(λ, c)`-quasi-geodesic has an O-equivalent diagram. That diagram has a relator cell whose external
contiguity arc is longer than `(1 - 13μ)` of the cell's boundary length. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    GroupApproximation.Full.GL06a.budget.{u, w, v}
    GroupApproximation.Full.GL06b.twoGonCleanCopy.{u, w, v}
    GroupApproximation.Full.GL06c.wholeSectionTwoArc.{u, w, v}
    (osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (GroupApproximation.Full.GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected
        GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{u, w, v}))
    (outerPinchStep_of_cases GroupApproximation.Full.GL06d.nonRoseStep.{u, w, v}
      (GroupApproximation.Full.GL06f.rose_of_regionMoveSubArc
        GroupApproximation.Full.GL03D.roseRegionMoveSubArc.{u, w, v}))

/-- The universe-`0` instance consumed by the torsion-free endpoints. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_zero :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

end GroupApproximation.Full.GL06

#audit_closed_axioms GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea
#audit_closed_axioms GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_zero
