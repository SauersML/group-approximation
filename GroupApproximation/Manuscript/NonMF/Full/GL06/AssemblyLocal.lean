import GroupApproximation.Manuscript.NonMF.Full.GL06.Waist
import GroupApproximation.Manuscript.NonMF.Full.GL06.BinderFive
import GroupApproximation.Manuscript.NonMF.Full.GL03B.FollowsCase
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
# GL06: Osin's Lemma 4.4 at least-area diagrams, through the original enclosed inner pocket

Osin, arXiv:math/0411039v3, Lemma 4.4, proved through Lemmas 9.4 and 9.7(b).  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex, around line 2121).  On its own it certifies no printed sentence.

This is the second of two variants of the GL06 assembly.  They differ only in the `hcopy` binder.

* `Full/GL06/Assembly` consumes `Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected` and the
  all-cells refutation `Full.GL06.EnclosedAllRelatorCellsRefutedSectionStatement`.
* This file consumes the original `Full.GL03B.InnerPocketEnclosedTwoArcLocal`.

GL03BPinch claims the original statement is false.  GL03B disputes the claim: in the proposed model
the face set `{C, H1, H2}` is a witness.  Until that is settled, both variants are kept.  Whichever
closes first carries the canonical name `Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea`, and
the other is then dropped.

* `hbudget`, `htwocopy`, `hwhole`, `hstep`: as in `Full/GL06/Assembly`.
* `hcopy`: `Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted` of PROVISIONAL
  `Full.GL06e.refutedBelowSection_of_innerPocketEnclosed :
    Full.GL03B.InnerPocketEnclosedTwoArcLocal → Full.GL06e.CellPocketWalkRefutedBelowSectionStatement`.
  It is applied to the landed `Full.GL03B.innerPocketEnclosedTwoArcLocal_of_pinched` of PROVISIONAL
  `Full.GL03BPinch.innerPocketEnclosedTwoArcPinched : Full.GL03B.InnerPocketEnclosedTwoArcPinchedLocal`.
  `Full.GL03B.Endpoint` is not imported, because its closure contains WIP `P07LakeExclusion` files.
-/

namespace GroupApproximation.Full.GL06

universe u w v

open GroupApproximation.GGT.VanKampen

/-- **Osin's Lemma 4.4 at least-area diagrams, original enclosed-pocket route** (relative
Greendlinger lemma; `thm:hull` infrastructure, non_mf_groups_exist.tex ~2121).  Same statement as
`Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_viaLocal :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    GroupApproximation.Full.GL06a.budget.{u, w, v}
    GroupApproximation.Full.GL06b.twoGonCleanCopy.{u, w, v}
    GroupApproximation.Full.GL06c.wholeSectionTwoArc.{u, w, v}
    (osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (GroupApproximation.Full.GL06e.refutedBelowSection_of_innerPocketEnclosed
        (GroupApproximation.Full.GL03B.innerPocketEnclosedTwoArcLocal_of_pinched
          GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcPinched.{u, w, v})))
    (outerPinchStep_of_cases GroupApproximation.Full.GL06d.nonRoseStep.{u, w, v}
      (GroupApproximation.Full.GL06f.rose_of_regionMoveSubArc
        GroupApproximation.Full.GL03D.roseRegionMoveSubArc.{u, w, v}))

/-- The universe-`0` instance of the original enclosed-pocket route. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_viaLocal_zero :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea_viaLocal.{0, 0, 0}

end GroupApproximation.Full.GL06

#audit_closed_axioms GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_viaLocal
#audit_closed_axioms GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_viaLocal_zero
