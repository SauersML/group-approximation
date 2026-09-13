import GroupApproximation.Dynamics.ClopenCrossedProductCountable
import GroupApproximation.Manuscript.ChainCore.BilateralThreeStatement
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Meta.AxiomGuard

/-!
# Producers of the two countability pieces

`non_mf_groups_exist.tex`, tex 1647–1649, "$X$ has a countable clopen basis and each clopen subset is
a finite union of basis sets".  Two lanes state the countability of `R_X` as a named piece Prop:

* `Manuscript.ChainCore.BilateralThree.ClopenCrossedProductCountableStatement`
  (prop:bilateral-three, residual 2);
* `ChainCore.DynamicRankBudget.CountableCrossedProductStatement` (cor:dynamic-rank-budget).

Both follow from `ClopenCrossedProduct.countable`
(`Dynamics/ClopenCrossedProductCountable.lean`).  This module only wraps it, so the light producer
module can be imported by either consumer without an import cycle.
-/

namespace GroupApproximation

/-- **Producer of `ClopenCrossedProductCountableStatement`** (ct-bilateral-mf). -/
theorem clopenCrossedProductCountableStatement :
    Manuscript.ChainCore.BilateralThree.ClopenCrossedProductCountableStatement :=
  fun _ _ _ _ _ T k _ _ ↦ ClopenCrossedProduct.countable T k

/-- **Producer of `CountableCrossedProductStatement`** (ct-rank-budget). -/
theorem countableCrossedProductStatement :
    ChainCore.DynamicRankBudget.CountableCrossedProductStatement :=
  fun _ _ _ _ T k _ _ ↦ ClopenCrossedProduct.countable T k

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.clopenCrossedProductCountableStatement
#audit_closed_axioms GroupApproximation.countableCrossedProductStatement
