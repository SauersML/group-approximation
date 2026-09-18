import GroupApproximation.Manuscript.NonMF.Full.GL06.Waist
import GroupApproximation.Manuscript.NonMF.Full.GL06a.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06b.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06c.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.TorsionFreeEndpoints.Reductions
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist with its closed residuals filled in

The Below waist `GL06.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals` takes five
residuals.  Three of them are closed: 01 (`GL06a.budget`), 05 (`GL06b.twoGonCleanCopy`) and 09
(`GL06c.wholeSectionTwoArc`).  This module fills them in.  Two inputs are left open: binder 5
(`hcopy`, the multiple-edge pocket region copy below the section count) and residual 10 (`hstep`,
the outer pinch step).

The same statement at universes `0, 0, 0` then gives the bundle
`Full.TorsionFreeEndpoints.TorsionFreeEndpoints` through `torsionFreeEndpoints_of_greendlinger`.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **Osin's Lemma 4.4 at least-area diagrams from binder 5 and residual 10** (Osin, Lemma 4.4
via Lemma 9.4 and Lemma 9.7(b); `thm:hull`).  The closed residuals 01, 05 and 09 are filled in. -/
theorem nmWire_greendlinger_of_copy_step
    (hcopy : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    GroupApproximation.Full.GL06a.budget GroupApproximation.Full.GL06b.twoGonCleanCopy
    GroupApproximation.Full.GL06c.wholeSectionTwoArc hcopy hstep

#audit_axioms GroupApproximation.Full.NMWire.nmWire_greendlinger_of_copy_step

/-- **The zero-parameter torsion-free endpoints from binder 5 and residual 10**, both at
universes `0, 0, 0`. -/
theorem nmWire_torsionFreeEndpoints_of_copy_step
    (hcopy : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{0, 0, 0})
    (hstep : PocketOuterPinchStepSectionStatement.{0, 0, 0}) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger
    (nmWire_greendlinger_of_copy_step hcopy hstep)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_torsionFreeEndpoints_of_copy_step

end GroupApproximation.Full.NMWire
