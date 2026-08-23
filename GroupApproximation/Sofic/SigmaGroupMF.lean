import GroupApproximation.Sofic.TerminalQuotientPresentation
import GroupApproximation.Sofic.WitnessVerticalResiduallyFinite
import GroupApproximation.Sofic.LocallyFiniteMF

/-!
# The compression source of the terminal amalgam is operator MF

`Sofic/TerminalQuotientIso` reduces the manuscript's exact MF-radical
computation to a single analytic input, operator MF of the symmetric double
`Σ *_B Σ`.  `Sofic/SymmetricDoubleMF` then shows the exact-model routes to that
input are closed: `B` is not separable in `Σ`, because `Σ` carries the
Baumslag--Solitar pattern `t v₁ t⁻¹ = v₁²` which degenerates in every finite
group, so the amalgam is neither residually finite nor `LEF`.

None of that touches `Σ` itself, and this file records the difference.  `Σ` is
residually finite, and residual finiteness reaches operator MF along a chain
this library already carries unconditionally:

```text
Group.ResiduallyFinite Σ  →  IsLEF Σ  →  IsOperatorMF Σ
```

* `WitnessVertical.vertical_residuallyFinite` proves the first, for
  `Vertical alpha conjD_injective`, which is `SigmaGroup` on the nose --
  `LiteralLampKernelSplit.V` unfolds to exactly that type.
* `LEFSofic.isLEF_of_residuallyFinite` and `LocallyFiniteMF.isOperatorMF_of_isLEF`
  are the two steps, and `MarkedCompressionGroup` supplies the `Countable`
  instance the second one reads.

## Why this is worth stating

Shulman's Theorem 10 concerns `A *_C A` for a *separable MF* algebra `A`.  The
group-side hypothesis it wants is exactly `IsOperatorMF Σ`, and that is now
discharged rather than assumed.  What remains for the exact radical is the
amalgamation step alone -- the passage from MF of the factor to MF of the
double -- and not any property of the factor.

The contrast with `SymmetricDoubleMF` is the whole content: the factor is MF by
an exact finite model, while the double provably is not reachable that way.  So
the two files together say the difficulty is created by the amalgamation and
by nothing else.
-/

namespace GroupApproximation
namespace TerminalQuotientPresentation

open WitnessVertical

/-- **The compression source is residually finite.**  `SigmaGroup` is
`LiteralLampKernelSplit.V`, which unfolds to `Vertical alpha conjD_injective`,
so this is `WitnessVertical.vertical_residuallyFinite` at the name the amalgam
uses. -/
theorem sigmaGroup_residuallyFinite : Group.ResiduallyFinite SigmaGroup :=
  vertical_residuallyFinite

/-- **The compression source is `LEF`.**  Residual finiteness is a local
embeddability certificate: the finite quotient separating the difference
quotients of a finite set is the finite model on that set. -/
theorem sigmaGroup_isLEF : IsLEF SigmaGroup := by
  letI : Group.ResiduallyFinite SigmaGroup := sigmaGroup_residuallyFinite
  exact isLEF_of_residuallyFinite

/-- **The compression source is operator MF.**

This is the group-side hypothesis of Shulman's theorem for the symmetric
double, discharged.  It does *not* give operator MF of the double:
`Sofic/SymmetricDoubleMF.exactModelRoute_closed` proves the amalgam is neither
residually finite nor `LEF`, so this chain stops at the factor. -/
theorem sigmaGroup_isOperatorMF : IsOperatorMF SigmaGroup :=
  isOperatorMF_of_isLEF sigmaGroup_isLEF

end TerminalQuotientPresentation
end GroupApproximation
