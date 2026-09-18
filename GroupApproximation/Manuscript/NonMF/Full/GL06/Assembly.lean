import GroupApproximation.Manuscript.NonMF.Full.GL06.Waist
import GroupApproximation.Manuscript.NonMF.Full.GL06.BinderFive
import GroupApproximation.Manuscript.NonMF.Full.GL06a.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06b.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06c.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06d.NonRose
import GroupApproximation.Manuscript.NonMF.Full.GL06e.AllCellsStatement
import GroupApproximation.Manuscript.NonMF.Full.GL06e.Refuted
import GroupApproximation.Manuscript.NonMF.Full.GL06f.Reduction
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL03D.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06: Osin's Lemma 4.4 at least-area diagrams, from two named residuals

The relative Greendlinger lemma at least-area diagrams:
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (module
`GGT.VanKampen.Estimating.OsinAppendixSections`). Source: Osin, arXiv:math/0411039v3, Lemma 4.4,
proved through Lemmas 9.4 and 9.7(b). This is the Greendlinger waist of Hull's small cancellation
theorem, `thm:hull` (non_mf_groups_exist.tex, around line 2121), used by the torsion-free results of
non_mf_groups_exist.tex. On its own it certifies no printed sentence.

**CONDITIONAL, stated loudly.**  The endpoints here take two hypotheses that are **not proved**
in the repository:
* `hall : Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement` (binder 5, the all-cells
  disjunct of the corrected enclosed inner pocket);
* `hcore : Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement` (residual 10, the planar kept
  sub-walk core of the rose sub-arc region move).
They are the minimal residual set `NMWire2.nmWire2_MinimalResiduals`.  An earlier version of this
module stated the lemma unconditionally, citing the nonexistent names
`Full.GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected` and
`Full.GL03D.roseRegionMoveSubArc`.  Those citations are replaced by the real conditional
declarations below, and the unconditional theorem is withdrawn.

Route: the Below waist with residuals as hypotheses,
`Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals` (`Full/GL06/Waist`), which
already supplies residual 04 (`Full.GL02.gapSpan`) and residual 08 (`P08ProperArc.proof`).
* `hbudget` (residual 01): `Full.GL06a.budget`.
* `htwocopy` (residual 05): `Full.GL06b.twoGonCleanCopy`.
* `hwhole` (residual 09): `Full.GL06c.wholeSectionTwoArc`.
* `hcopy` (binder 5, residuals 06 and 07):
  `Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted` (`Full/GL06/BinderFive`)
  applied to `Full.GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells`, fed
  the proved `Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected` and the hypothesis `hall`.  The
  original `Full.GL03B.InnerPocketEnclosedTwoArcLocal` is false (GL03BPinch), so it is not
  consumed.
* `hstep` (residual 10): `Full.GL06.outerPinchStep_of_cases` of `Full.GL06d.nonRoseStep` and
  `Full.GL06f.rose_of_regionMoveSubArc`, applied to
  `Full.GL03D.gl03dKept_roseRegionMoveSubArc_of_core` of the hypothesis `hcore`.

GL05c's counterexample (fk/orders/GL05c-counterexample.md) killed the rose junction route
(`P10RoseExtremalTrim.RoseExtremalJunctionStatement`, GL03C Endpoint). The rose step is consumed
only through the sub-arc region move.
-/

namespace GroupApproximation.Full.GL06

universe u w v

open GroupApproximation.GGT.VanKampen

/-- **Osin's Lemma 4.4 at least-area diagrams, CONDITIONAL on two residuals** (relative
Greendlinger lemma; `thm:hull` infrastructure, non_mf_groups_exist.tex ~2121).

**The hypotheses `hall` and `hcore` are not proved in the repository.**  Given them: take a
hyperbolic relative generating set and `0 < λ ≤ 1`, `0 ≤ c`, `0 < μ ≤ 1/16`. Then there are `ε` and
`ρ > 0` with the following property. Every least-area disc diagram over a `C(ε, μ, λ, c, ρ)`
relator set whose boundary is `(λ, c)`-quasi-geodesic has an O-equivalent diagram. That diagram
has a relator cell whose external contiguity arc is longer than `(1 - 13μ)` of the cell's
boundary length. -/
theorem relativeGreendlinger_of_allCells_of_core
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v})
    (hcore : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    GroupApproximation.Full.GL06a.budget.{u, w, v}
    GroupApproximation.Full.GL06b.twoGonCleanCopy.{u, w, v}
    GroupApproximation.Full.GL06c.wholeSectionTwoArc.{u, w, v}
    (osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells
        GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{u, w, v} hall))
    (outerPinchStep_of_cases GroupApproximation.Full.GL06d.nonRoseStep.{u, w, v}
      (GroupApproximation.Full.GL06f.rose_of_regionMoveSubArc
        (GroupApproximation.Full.GL03D.gl03dKept_roseRegionMoveSubArc_of_core hcore)))

/-- The universe-`0` instance of `relativeGreendlinger_of_allCells_of_core`,
**CONDITIONAL on the same two unproved residuals**. -/
theorem relativeGreendlinger_zero_of_allCells_of_core
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hcore : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlinger_of_allCells_of_core.{0, 0, 0} hall hcore

end GroupApproximation.Full.GL06

#audit_axioms GroupApproximation.Full.GL06.relativeGreendlinger_of_allCells_of_core
#audit_axioms GroupApproximation.Full.GL06.relativeGreendlinger_zero_of_allCells_of_core
