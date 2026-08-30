import GroupApproximation.Analysis.VoiculescuProjectionAssembly
import GroupApproximation.Analysis.VoiculescuQuasicentralDiagonal

/-!
# (V1) Arveson's quasicentral approximate unit, unconditionally

`Analysis/VoiculescuQuasicentralStatement` records that the plan's
`QuasicentralApproximateUnitStatement` is false as written, and states the
repaired form with `[SeparableSpace H]`.  This module proves the repaired form:
(V1a) supplies a sequential approximate unit for the compacts, and (V1b) makes
it asymptotically central for the given countable family.

The separability is spent exactly once, in (V1a), on turning the ideal's
approximate unit from a net into a sequence — which is the refutation's own
mechanism seen from the other side, and confirms that the repair was minimal:
the quasicentrality half never asks for it.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-- **The repaired statement, discharged.**  On a separable Hilbert space the
compacts have a sequential approximate unit that is asymptotically central for
any countable family of bounded operators. -/
theorem quasicentralApproximateUnitSeparable :
    QuasicentralApproximateUnitSeparableStatement := by
  intro H _ _ _ _ S
  obtain ⟨u⟩ := nonempty_sequentialCompactUnit H
  exact exists_quasicentral_of_sequentialCompactUnit u S

end

end ShulmanFill
end GroupApproximation
