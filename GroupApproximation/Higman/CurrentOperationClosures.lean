import GroupApproximation.Higman.SsetBaseCase
import GroupApproximation.Higman.RowDeletionGraph

/-!
# The current boundary for Higman's operation closures

The older assembly theorems still expose inputs that have since been proved.
This module records the exact present dependency table and removes those
stale arguments.

* `base` is `Seq.benignTF_ASub_Sset`;
* `rho` is `operationClosures_rho`;
* `tau` remains the transposition closure;
* the positive-half, `ζ`, and even-deletion rows are discharged by
  `RowDeletionGraph`;
* `theta`, `zeta`, `pi`, and `omega` therefore need only `Omega.OmegaInput`.

Thus `OperationClosures` currently costs exactly two inputs: `Omega.OmegaInput`
and the transposition closure.
-/

namespace GroupApproximation
namespace Higman

/-- **`OperationClosures` from the two presently unresolved leaves.** -/
theorem operationClosures_of_two_inputs (k : Omega.OmegaInput)
    (htau : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
      BenignTF (Seq.ASub (Seq.tauOp B))) :
    OperationClosures :=
  operationClosures_of_five_inputs k htau benignTF_rowSub_piV
    RowDeletionGraph.zeta_row_benignTF
    RowDeletionGraph.evenDeletion_row_benignTF

end Higman
end GroupApproximation
