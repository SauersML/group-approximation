import GroupApproximation.BooneHigman.Join.DFinal
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDoneSwap

/-!
# `hswap`, unconditionally (lane bh-pal-met-join)

`higmanVSwapSection_uncond : HigmanVSwapSectionStatement`.  It is half (1) of the transfer for
every alphabet (`higmanVC_ker_le_all`), fed to `higmanVCTauDone_swapSection_of_ker_le`.
-/

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The swap-section statement for Higman's `V_d`, with no hypotheses.** -/
theorem higmanVSwapSection_uncond : HigmanVSwapSectionStatement :=
  higmanVCTauDone_swapSection_of_ker_le higmanVC_ker_le_all

#audit_axioms GroupApproximation.BooneHigman.Join.higmanVSwapSection_uncond

end GroupApproximation.BooneHigman.Join
