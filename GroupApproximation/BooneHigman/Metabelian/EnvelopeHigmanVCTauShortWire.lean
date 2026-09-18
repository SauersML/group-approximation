import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauShortReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauConjWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The `τ` half from the short-conjugator residual

Lane bh-met-77j reduces `HigmanVCTauConjShortStatement` to `HigmanVCTauShortResidualStatement`
(oriented top-level instances where all-short, option E and option A all fail). This file
composes that reduction with `EnvelopeHigmanVCTauConjWire.lean`.

**LOUD.** The residual is EQUIVALENT to the short statement (`higmanVCTauShort_residual_iff`),
not strictly weaker; only its proof content is smaller.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `HigmanVCTauConjStatement` from the short-conjugator residual. -/
theorem higmanVCTauShortWire_conj_of_residual (hR : HigmanVCTauShortResidualStatement) :
    HigmanVCTauConjStatement :=
  higmanVCTauConjWire_conj_of_short (higmanVCTauShort_short_of_residual hR)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShortWire_conj_of_residual

/-- **The `τ` half (`hB`) from the short-conjugator residual alone.** -/
theorem higmanVCTauShortWire_tau_of_residual (hR : HigmanVCTauShortResidualStatement) :
    HigmanVCTauStatement :=
  higmanVCTauConjWire_tau_of_short (higmanVCTauShort_short_of_residual hR)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShortWire_tau_of_residual

end GroupApproximation.BooneHigman.Metabelian.Envelope
