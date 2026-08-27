import GroupApproximation.Higman.CurrentREBenign

/-!
# The ω-closure, as the repository's single recorded debt

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
for itself, so the kernel's axiom report carried two `sorry`s for one statement.
This module is that statement, once, and both lanes import it.

The module sits under `Higman/` rather than under either lane's directory
because `Manuscript.MFRecognition.SeedFromTheoremC` imports
`Manuscript.NonMF.TheoremCDebts`: the two debt files cannot import each other,
and this is the deepest point below both.

`set_option warningAsError false` is what lets the `sorry` stand.  Nothing else
in this module is unproved, and no other declaration in the repository should
restate `Nonempty Higman.Omega.OmegaInput` as a debt of its own.
-/

set_option warningAsError false

namespace GroupApproximation
namespace Higman
namespace OmegaDebt

/-- **DEBT (construction).**  Higman's ω-closure: the three-stage tower proving
that `ωₘ` preserves benignness.  This is the sole remaining input of the
benign-subgroup route to Higman's embedding theorem, and the only `sorry` in the
repository asserting it. -/
theorem omegaInput_nonempty : Nonempty Higman.Omega.OmegaInput := by
  sorry

/-- The ω-closure, as a term. -/
noncomputable def omegaInput : Higman.Omega.OmegaInput := omegaInput_nonempty.some

/-- **Higman's embedding theorem** — recursively enumerable normal subgroups of
finitely generated free groups are benign — on the ω-debt.  Recorded here so
that the two lanes share the consequence as well as the debt. -/
theorem reBenign : Higman.REBenign := Higman.reBenign_of_omega omegaInput

end OmegaDebt
end Higman
end GroupApproximation
