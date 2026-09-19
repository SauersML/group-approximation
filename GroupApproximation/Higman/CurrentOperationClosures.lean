import GroupApproximation.Higman.SsetBaseCase
import GroupApproximation.Higman.RowDeletionGraph

/-!
# The current boundary for Higman's operation closures

The older assembly theorems still expose inputs that have since been proved.
This module records the exact present dependency table and removes those
stale arguments.

* `base` is `Seq.benignTF_ASub_Sset`;
* `rho` is `operationClosures_rho`;
* the formalized generated-set construction never uses `tau`, so it is not a
  constructor and creates no closure obligation;
* the positive-half, `ζ`, and even-deletion rows are discharged by
  `RowDeletionGraph`;
* `theta`, `zeta`, `pi`, and `omega` therefore need only `Omega.OmegaInput`.

Thus `OperationClosures` currently costs exactly one input:
`Omega.OmegaInput`.
-/

namespace GroupApproximation
namespace Higman

/-- **`OperationClosures` from its sole presently unresolved leaf.** -/
theorem operationClosures_of_omega (k : Omega.OmegaInput) :
    OperationClosures :=
  operationClosures_of_omega_and_rows k benignTF_rowSub_piV
    RowDeletionGraph.zeta_row_benignTF
    RowDeletionGraph.evenDeletion_row_benignTF

end Higman
end GroupApproximation
