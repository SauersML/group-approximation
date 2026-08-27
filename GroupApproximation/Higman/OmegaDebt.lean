import GroupApproximation.Higman.CurrentREBenign
import GroupApproximation.Higman.OmegaFillLeadLinkBenign

/-!
# The ω-closure, once, for both lanes

`Higman.Omega.OmegaInput` is the one construction the benign-subgroup route to
Higman's embedding theorem still owes: the three-stage tower proving that
Higman's operation `ωₘ` preserves benignness.  Everything else on that route is
proved — `Higman.higmanTheoremThree`, `Higman.PairedReturnCutter.transportSectionFive`
and `Higman.BridgePresentation.bridgeEffective` are unconditional, and
`Higman.operationClosures_of_omega` reduces the remaining operation closures to
the tower.

Two lanes stand on it.  The recognition lane reaches Higman's embedding theorem
through `Higman.reBenign_of_omega`, and the Theorem C lane reaches Chiodo's
Theorem 3.10 through
`Manuscript.NonMF.TheoremC.chiodo_of_omega`.  Each lane used to record the debt
for itself; this module is the statement, once, and both lanes import it.

The module sits under `Higman/` rather than under either lane's directory
because `Manuscript.MFRecognition.SeedFromTheoremC` imports
`Manuscript.NonMF.TheoremCDebts`: the two debt files cannot import each other,
and this is the deepest point below both.

Since `Higman.OmegaFillLeadLinkBenign` the statement is a theorem, not a
debt; this module remains the one place both lanes read it from.
-/

namespace GroupApproximation
namespace Higman
namespace OmegaDebt

/-- **Higman's ω-closure**, proved: the slim tower's Britton descent
(`Omega.slimDescent`) and the benignness of the sheared link
(`Omega.LeadLink.benignTF_fatShearedBlockLink`, Mikaelian's Examples 3.10–3.12
in the fat first stage).  Kept under its historical name so that both lanes
keep importing one declaration. -/
theorem omegaInput_nonempty : Nonempty Higman.Omega.OmegaInput :=
  Higman.Omega.omegaInput_nonempty

/-- The ω-closure, as a term. -/
noncomputable def omegaInput : Higman.Omega.OmegaInput := omegaInput_nonempty.some

/-- **Higman's embedding theorem** — recursively enumerable normal subgroups of
finitely generated free groups are benign — on the ω-debt.  Recorded here so
that the two lanes share the consequence as well as the debt. -/
theorem reBenign : Higman.REBenign := Higman.reBenign_of_omega omegaInput

end OmegaDebt
end Higman
end GroupApproximation
