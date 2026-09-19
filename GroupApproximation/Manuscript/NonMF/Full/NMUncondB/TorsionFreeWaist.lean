import GroupApproximation.Manuscript.NonMF.Full.TorsionFreeEndpoints.Closed
import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly
import GroupApproximation.Manuscript.NonMF.Full.GL06e.AllCellsStatement
import GroupApproximation.Manuscript.NonMF.Full.GL03DKept.Core
import GroupApproximation.Meta.AxiomGuard

/-!
# The torsion-free endpoints over one named waist Prop, CONDITIONAL

**CONDITIONAL, stated loudly.**  Every theorem here takes `h : TorsionFreeWaistResiduals`, and
that Prop is **not proved in the repository**.

`non_mf_groups_exist.tex`, `sec:torsion-free`: `thm:torsion-free` with its Osin and limit-set
variants, `thm:hull`, `lem:saturation`, the Fournier-Facio paragraph,
`cor:regular-nonmf-algebra`, abstract tex 78–79, and introduction tex 292–293 and 303–305.
All of these are the conjuncts of `Full.TorsionFreeEndpoints.TorsionFreeEndpoints`.

## What is still open

`Full/TorsionFreeEndpoints/Closed` proves every endpoint from the relative Greendlinger lemma
`hG` (Osin, arXiv:math/0411039v3, Lemma 4.4).  `Full.GL06.relativeGreendlinger_zero_of_allCells_of_core`
proves `hG` from two residuals of the induction step of Osin's Lemma 9.7(b):

* `Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement` (binder 5);
* `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement` (residual 10).

Every other input of the section is closed on main (Hull Corollary 5.7 and Lemmas 3.5 and 5.8,
the embedded bridge behind Hull Corollary 7.4, Kotowski–Ollivier, the Hyde–Lodha group,
DGO 2.35, Gerasimova–Osin 1.1).  So `TorsionFreeWaistResiduals`, the conjunction of these two
residuals at universes `0, 0, 0`, is the **only** open input of the section.

## The one-line discharge

This module fixes the interface.  Once both residuals are proved,
`NMUncondB/TorsionFreeUnconditional` (staged in lane ms-nm-uncond-b) supplies
`torsionFreeWaistResiduals_holds : TorsionFreeWaistResiduals` in one line and derives the closed
endpoints from the theorems below.  Nothing else in the section has to change.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMUncondB

open GroupApproximation.Full.TorsionFreeEndpoints

/-- **The two open residuals of the torsion-free section**, at universes `0, 0, 0`: binder 5 of
the enclosed inner pocket (all-cells disjunct) and residual 10 (planar kept sub-walk core), both
from the induction step of Osin, arXiv:math/0411039v3, Lemma 9.7(b).  **Not proved in the
repository.** -/
def TorsionFreeWaistResiduals : Prop :=
  GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0} ∧
    GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}

#audit_axioms GroupApproximation.Full.NMUncondB.TorsionFreeWaistResiduals

/-- The relative Greendlinger lemma at least-area diagrams (Osin Lemma 4.4), **CONDITIONAL on
`h`** (not proved in the repository). -/
theorem relativeGreendlinger_of_waistResiduals (h : TorsionFreeWaistResiduals) :
    GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  GL06.relativeGreendlinger_zero_of_allCells_of_core h.1 h.2

#audit_axioms GroupApproximation.Full.NMUncondB.relativeGreendlinger_of_waistResiduals

/-- **Every zero-parameter torsion-free endpoint, CONDITIONAL on `h`** (not proved in the
repository): `torsionFreeEndpoints_closed_of_greendlinger` at
`relativeGreendlinger_of_waistResiduals h`. -/
theorem torsionFreeEndpoints_of_waistResiduals (h : TorsionFreeWaistResiduals) :
    TorsionFreeEndpoints :=
  torsionFreeEndpoints_closed_of_greendlinger (relativeGreendlinger_of_waistResiduals h)

#audit_axioms GroupApproximation.Full.NMUncondB.torsionFreeEndpoints_of_waistResiduals

/-- Abstract, tex 78–79, **CONDITIONAL on `h`** (not proved in the repository). -/
theorem abstractTorsionFreeClause_of_waistResiduals (h : TorsionFreeWaistResiduals) :
    AbstractTorsionFreeClause :=
  abstractTorsionFreeClause_closed_of_greendlinger (relativeGreendlinger_of_waistResiduals h)

#audit_axioms GroupApproximation.Full.NMUncondB.abstractTorsionFreeClause_of_waistResiduals

/-- Introduction, tex 292–293, "The last group has none", **CONDITIONAL on `h`** (not proved in
the repository). -/
theorem introLastGroupHasNone_of_waistResiduals (h : TorsionFreeWaistResiduals) :
    IntroLastGroupHasNone :=
  introLastGroupHasNone_closed_of_greendlinger (relativeGreendlinger_of_waistResiduals h)

#audit_axioms GroupApproximation.Full.NMUncondB.introLastGroupHasNone_of_waistResiduals

/-- Introduction, tex 303–305, **CONDITIONAL on `h`** (not proved in the repository). -/
theorem introReducedAlgebraSentence_of_waistResiduals (h : TorsionFreeWaistResiduals) :
    IntroReducedAlgebraSentence :=
  introReducedAlgebraSentence_closed_of_greendlinger (relativeGreendlinger_of_waistResiduals h)

#audit_axioms GroupApproximation.Full.NMUncondB.introReducedAlgebraSentence_of_waistResiduals

end GroupApproximation.Full.NMUncondB
