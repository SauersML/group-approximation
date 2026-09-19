import GroupApproximation.Higman.CurrentOperationClosures
import GroupApproximation.Higman.EnumeratedRangeClosed
import GroupApproximation.Higman.PairedReturnCutter
import GroupApproximation.Higman.TheoremFour

/-!
# The current one-leaf assembly of Higman's embedding theorem

The repository has now discharged every part of the benign-subgroup route
except one concrete construction:

* the three-stage tower proving closure under `omegaOp`.

The base cases and all other operation closures are assembled by
`operationClosures_of_omega`.  Higman's Section 2 is the unconditional theorem
`higmanTheoremThree`, and Section 5 is the unconditional five-generator cutter
`PairedReturnCutter.transportSectionFive`.

This file records their direct composite.  In particular, it prevents the
finished Section 5 theorem from remaining hidden behind the old three-input
interface in `TheoremFour`.
-/

namespace GroupApproximation
namespace Higman

/-- Omega is the sole remaining input to the torsion-free form of Higman's
r.e.-subgroup theorem. -/
theorem reBenignTF_of_omega (hOmega : Omega.OmegaInput) : REBenignTF :=
  reBenignTF_of_inputs
    (operationClosures_of_omega hOmega)
    higmanTheoremThree
    PairedReturnCutter.transportSectionFive

/-- Ordinary recursively-enumerable benignity now depends only on Omega. -/
theorem reBenign_of_omega (hOmega : Omega.OmegaInput) : REBenign :=
  reBenign_of_reBenignTF (reBenignTF_of_omega hOmega)

/-- The current finitely-generated embedding theorem has exactly the Omega
tower as its remaining input. -/
theorem fpOvergroup_of_fgRecursive_of_omega
    (hOmega : Omega.OmegaInput) {G : Type} [Group G]
    (p : FGRecursive G) : Nonempty (FPOvergroup G) :=
  fpOvergroup_of_fgRecursive (reBenign_of_omega hOmega) p

end Higman
end GroupApproximation
