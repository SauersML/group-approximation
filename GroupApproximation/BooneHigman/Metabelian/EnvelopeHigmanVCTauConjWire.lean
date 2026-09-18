import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauConjFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# The `τ` half, wired: split family proved, conjugation family reduced to short conjugators

Lane bh-met-77f proves the split family outright and reduces `HigmanVCTauStatement` to
`HigmanVCTauConjStatement`. Lane bh-met-77g declares the same statement as
`HigmanVCTauConjFamilyStatement` and reduces it to `HigmanVCTauConjShortStatement` (short
conjugator, some long letter). This file identifies the two and composes the reductions.

**LOUD.** `HigmanVCTauConjShortStatement` is EQUIVALENT to the conjugation family
(`higmanVCTauConj_family_iff_short`), not strictly weaker; only its proof content is smaller.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The two lanes' conjugation statements coincide. -/
theorem higmanVCTauConjWire_conj_iff_family :
    HigmanVCTauConjStatement ↔ HigmanVCTauConjFamilyStatement :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConjWire_conj_iff_family

/-- `HigmanVCTauConjStatement` from the short-conjugator gap. -/
theorem higmanVCTauConjWire_conj_of_short (hS : HigmanVCTauConjShortStatement) :
    HigmanVCTauConjStatement :=
  higmanVCTauConj_conjFamily_of_short hS

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConjWire_conj_of_short

/-- `HigmanVCTauConjSplitStatement` from the short-conjugator gap. -/
theorem higmanVCTauConjWire_conjSplit_of_short (hS : HigmanVCTauConjShortStatement) :
    HigmanVCTauConjSplitStatement :=
  higmanVCTauSplit_conjSplit_of_conj (higmanVCTauConjWire_conj_of_short hS)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConjWire_conjSplit_of_short

/-- **The `τ` half (`hB`) from the short-conjugator gap alone.** -/
theorem higmanVCTauConjWire_tau_of_short (hS : HigmanVCTauConjShortStatement) :
    HigmanVCTauStatement :=
  higmanVCTauSplit_tau_of_conj (higmanVCTauConjWire_conj_of_short hS)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConjWire_tau_of_short

end GroupApproximation.BooneHigman.Metabelian.Envelope
