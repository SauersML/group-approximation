import GroupApproximation.Higman.OmegaFillSlimClosure
import GroupApproximation.Higman.OmegaTowerStaticSeamClosed

/-!
# The slim descent, substituted

`Higman.OmegaFillSlimClosure` reduces Higman's `ωₘ` closure to a benignness
statement about the slim tower, keeping the Britton half as the named
hypothesis `Omega.SlimDescent`.  That hypothesis is
`Omega.slimTower_descent`, the end of the normal-form chain that begins in
`Higman.OmegaTowerDescent`, and this file is the one line that substitutes it.

After it, `Omega.OmegaInput` --- the last open input of Higman's Theorem 3 on
this lane --- is exactly `Omega.SlimWBenign`, and equally exactly
`Omega.SlimLinkedBenignTower`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- **The slim tower has the descent.** -/
theorem slimDescent : SlimDescent :=
  fun _ hm _ h0 => slimTower_descent hm h0

/-- **Higman's `ωₘ` closure is exactly benignness of `W_B` in the slim
tower.** -/
theorem omegaInput_of_slimWBenign' (h : SlimWBenign) : OmegaInput :=
  omegaInput_of_slimWBenign slimDescent h

/-- **... and equally exactly a benign tower receiving the slim one.** -/
theorem omegaInput_of_slimLinked' (h : SlimLinkedBenignTower) : OmegaInput :=
  omegaInput_of_slimLinked slimDescent h

end Omega
end Higman
end GroupApproximation
