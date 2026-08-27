import GroupApproximation.Manuscript.NonMF.TheoremCPrinted

/-!
# Theorem C, closed: the cited inputs as recorded debts

`TorsionFreeTheoremC.manuscriptTorsionFreeFullMFRadical` proves Theorem C
from two bundles of cited results: Fournier-Facio's paragraph
(`TheoremC.LiteratureInputs`: Chiodo, Kotowski–Ollivier–Wise, Fournier-Facio
et al. with Osin, Minasyan–Osin, Hull's common quotient theorem) and Hull's
small cancellation theorem with its companions (`TorsionFree.HullInputs`).

This module records each bundle as a declaration whose proof is `sorry`, so
that the debt is visible in the kernel's axiom report rather than hidden in a
leading binder, and closes the two printed statements of Theorem C on top of
them.  Every `sorry` here is a theorem of the literature that this development
has not yet proved; the names say which.
-/

set_option warningAsError false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

/-- **DEBT (literature).**  Fournier-Facio's paragraph: Chiodo's universal
torsion-free group, the Kotowski–Ollivier–Wise density model, the
small-cancellation quotient of Fournier-Facio et al. with Osin, Minasyan–Osin,
and Hull's common quotient theorem. -/
theorem literatureInputs_nonempty : Nonempty LiteratureInputs := by
  sorry

/-- **DEBT (literature).**  Hull, Theorem 7.1 with its construction remark,
Osin's Lemma 7.1, and Hull's Corollary 5.7 with Lemma 5.8. -/
theorem hullInputs_nonempty : Nonempty TorsionFree.HullInputs.{0} := by
  sorry

/-- The cited inputs, as a term. -/
noncomputable def literatureInputs : LiteratureInputs := literatureInputs_nonempty.some

/-- Hull's inputs, as a term. -/
noncomputable def hullInputs : TorsionFree.HullInputs.{0} := hullInputs_nonempty.some

/-- **Theorem C (`thm:torsion-free`), in radical form, as a closed
declaration** on the recorded debts. -/
theorem manuscriptTorsionFreeFullMFRadical_closed : PrintedTorsionFreeFullMFRadical :=
  manuscriptTorsionFreeFullMFRadical literatureInputs hullInputs

/-- **Theorem C, in the simplified printed statement, as a closed
declaration** on the recorded debts. -/
theorem manuscriptTorsionFreeSimplified_closed : PrintedTorsionFreeSimplified :=
  manuscriptTorsionFreeSimplified literatureInputs hullInputs

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
