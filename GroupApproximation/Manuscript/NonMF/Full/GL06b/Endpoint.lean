import GroupApproximation.Manuscript.NonMF.Full.GL06b.OuterSteps
import GroupApproximation.Manuscript.NonMF.Full.GL06b.CellHair
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.Proof
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonCleanCopy
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06b endpoint: the clean two-gon copy section (residual 05)

This module is the endpoint that `Full/GL06/Assembly.lean` imports.  It proves
`twoGonCleanCopy : OsinTwoGonCleanCopySectionStatement`, which is the `htwocopy` residual of
`Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`.

The proof applies `osinTwoGonCleanCopySection_of_steps` to its six step inputs:

* spur, outer-cell and outer-side steps: `GL06b.OuterSteps`;
* cell-side step: `GreendlingerLeaf.P05CellSide.proof`;
* cell-hair step: `GL06b.CellHair`;
* region-pair step: `GreendlingerLeaf.P05RegionPair.proof`.

None of these inputs goes through the WIP-tainted `ClosedTrio` route.
-/

namespace GroupApproximation.Full.GL06b

open GroupApproximation.GGT.VanKampen

universe u w v

/-- Residual 05, the clean-copy section of an Osin two-gon, assembled from the six proved
step lemmas. -/
theorem twoGonCleanCopy : OsinTwoGonCleanCopySectionStatement.{u, w, v} :=
  osinTwoGonCleanCopySection_of_steps twoGonSpurStep twoGonOuterCellStep twoGonOuterSideStep
    GreendlingerLeaf.P05CellSide.proof twoGonCellHairStep GreendlingerLeaf.P05RegionPair.proof

#audit_axioms GroupApproximation.Full.GL06b.twoGonCleanCopy

end GroupApproximation.Full.GL06b
