import GroupApproximation.Higman.CurrentOperationClosures
import GroupApproximation.Higman.EnumeratedRangeExtract
import GroupApproximation.Higman.PairedReturnCutter
import GroupApproximation.Higman.TheoremFour

/-!
# The current two-leaf assembly of Higman's embedding theorem

The repository has now discharged every part of the benign-subgroup route
except two concrete constructions:

* the three-stage tower proving closure under `omegaOp`;
* the primitive-recursive construction of generated finite-window relations.

The base cases and all other operation closures are assembled by
`operationClosures_of_omega`.  Higman's Section 2 is assembled from the
bounded-window construction by `enumeratedRangeGenerated_of_boundedWindowRE`,
and Section 5 is the unconditional five-generator paired-return cutter
`PairedReturnCutter.transportSectionFive`.

This file records their direct composite.  In particular, it prevents the
finished Section 5 theorem from remaining hidden behind the old three-input
interface in `TheoremFour`.
-/

namespace GroupApproximation
namespace Higman

/-- A concrete Omega-tower closure and bounded-window generation give the
torsion-free form of Higman's r.e.-subgroup theorem. -/
theorem reBenignTF_of_omega_boundedWindow
    (hOmega : Omega.OmegaInput) (hWindow : BoundedWindowRE) : REBenignTF :=
  reBenignTF_of_inputs
    (operationClosures_of_omega hOmega)
    (higmanTheoremThree_of_enumeratedRange
      (enumeratedRangeGenerated_of_boundedWindowRE hWindow))
    PairedReturnCutter.transportSectionFive

/-- The ordinary benign-subgroup theorem needed by the finitely generated
Higman embedding follows from the same two concrete leaves. -/
theorem reBenign_of_omega_boundedWindow
    (hOmega : Omega.OmegaInput) (hWindow : BoundedWindowRE) : REBenign :=
  reBenign_of_reBenignTF (reBenignTF_of_omega_boundedWindow hOmega hWindow)

/-- The finitely generated Higman embedding theorem, with its complete current
dependency surface exposed: only the Omega tower and bounded-window
generation remain as inputs. -/
theorem fpOvergroup_of_fgRecursive_of_omega_boundedWindow
    (hOmega : Omega.OmegaInput) (hWindow : BoundedWindowRE)
    {G : Type} [Group G] (p : FGRecursive G) : Nonempty (FPOvergroup G) :=
  fpOvergroup_of_fgRecursive
    (reBenign_of_omega_boundedWindow hOmega hWindow) p

end Higman
end GroupApproximation
