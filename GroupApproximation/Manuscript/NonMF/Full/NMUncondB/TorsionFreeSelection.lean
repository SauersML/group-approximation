import GroupApproximation.Manuscript.NonMF.Full.NMUncondB.TorsionFreeWaist
import GroupApproximation.Manuscript.NonMF.Full.GL03DQuadrant.Waist
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free endpoints over binder 5 and the local selection, CONDITIONAL

**CONDITIONAL, stated loudly.**  Every theorem here takes two hypotheses, and neither is proved in
the repository:

* `hall : Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0}` (binder 5);
* `hsel : GreendlingerLeaf.P10LocalSelect.p10LS_SelectionStatement.{0}` (the local selection of a
  good lobe, step 2 of lane nm-gl03d's plan).

`non_mf_groups_exist.tex`, `sec:torsion-free`: the conjuncts of
`Full.TorsionFreeEndpoints.TorsionFreeEndpoints`.  This is the route of `NMUncondB/TorsionFreeWaist`
with residual 10 replaced by the selection statement:

* `P10LocalSelect.p10LS_quadrantMove_of_selection` gives the quadrant move;
* `Full.GL03DQuadrant.relativeGreendlinger_zero_of_allCells_of_quadrantMove` (lane nm-gl03d) gives
  the relative Greendlinger lemma (Osin Lemma 4.4) from binder 5 and the quadrant move;
* `Full.TorsionFreeEndpoints.torsionFreeEndpoints_closed_of_greendlinger` gives the endpoints.

Once `hall` and `hsel` are proved, the staged `NMUncondB/TorsionFreeUnconditional` closes
everything, with one proof line.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMUncondB

open GroupApproximation.Full.TorsionFreeEndpoints

/-- The relative Greendlinger lemma at least-area diagrams (Osin Lemma 4.4), **CONDITIONAL on
`hall` and `hsel`** (neither proved in the repository). -/
theorem relativeGreendlinger_of_allCells_of_selection
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hsel : GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionStatement.{0}) :
    GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  GL03DQuadrant.relativeGreendlinger_zero_of_allCells_of_quadrantMove hall
    (GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_quadrantMove_of_selection hsel)

#audit_axioms GroupApproximation.Full.NMUncondB.relativeGreendlinger_of_allCells_of_selection

/-- **Every zero-parameter torsion-free endpoint, CONDITIONAL on `hall` and `hsel`** (neither
proved in the repository). -/
theorem torsionFreeEndpoints_of_allCells_of_selection
    (hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hsel : GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionStatement.{0}) :
    TorsionFreeEndpoints :=
  torsionFreeEndpoints_closed_of_greendlinger
    (relativeGreendlinger_of_allCells_of_selection hall hsel)

#audit_axioms GroupApproximation.Full.NMUncondB.torsionFreeEndpoints_of_allCells_of_selection

end GroupApproximation.Full.NMUncondB
