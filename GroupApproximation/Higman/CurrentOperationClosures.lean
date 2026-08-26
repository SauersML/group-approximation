import GroupApproximation.Higman.SsetBaseCase
import GroupApproximation.Higman.RowDeletionBenign

/-!
# The current boundary for Higman's operation closures

The older assembly theorems still expose inputs that have since been proved.
This module records the exact present dependency table and removes those
stale arguments.

* `base` is `Seq.benignTF_ASub_Sset`;
* `rho` is `operationClosures_rho`;
* `tau` remains the transposition closure;
* `theta` needs `Omega.OmegaInput` and the even-deletion row;
* `zeta`, `pi`, and `omega` need `Omega.OmegaInput` and the `zeta` row;
* their former positive-half-row input is
  `benignTF_rowSub_piV` and is no longer open.

Thus `OperationClosures` currently costs exactly four inputs, not the five or
six shown by the older convenience constructors.
-/

namespace GroupApproximation
namespace Higman

/-- **`OperationClosures` from the four presently unresolved leaves.** -/
theorem operationClosures_of_four_inputs (k : Omega.OmegaInput)
    (htau : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
      BenignTF (Seq.ASub (Seq.tauOp B)))
    (hzetaRow : BenignTF (Agree.rowSub Agree.zetaV))
    (hevenRow :
      BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx)))) :
    OperationClosures :=
  operationClosures_of_five_inputs k htau benignTF_rowSub_piV hzetaRow hevenRow

end Higman
end GroupApproximation
