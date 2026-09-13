import GroupApproximation.SurjunctiveNonsofic.LaurentPairKazhdan
import GroupApproximation.SurjunctiveNonsofic.WreathWitness
import GroupApproximation.KunThom.CompressorNormalizationCore
import GroupApproximation.Sofic.GeneralizedWreathSofic
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.SoficPositiveControl

/-!
# The Kun–Thom coset action is not sofic

The coset action `Ambient ↷ Ambient ⧸ Peripheral` of the explicit pair

```text
Γ = EL₃(𝔽₂[x₁, x₂, x₃])  ≤  G = EL₃(𝔽₂[x₁^±¹, x₂^±¹, x₃^±¹]) ⋊ EL₃(ℤ)
```

is not sofic, although `G` is sofic.

`Ambient` is residually finite, hence LEF, hence sofic, and `ℤ/2` is finite.
A sofic coset action would make the coset wreath product `(ℤ/2) ≀_{G/Γ} G`
sofic, by Theorem 3.6 of Gao–Kunnawalkam Elayavalli–Patchell
(arXiv:2401.04945v3), formalized as `GeneralizedWreath.isSofic_wreath`.  That
wreath product is not sofic: `Peripheral` is infranormal and not normal, and
both groups have property (T), so Kun–Thom Theorem 4.1
(`hasSequentialCentralizerNormalization_of_kazhdan_infranormal`) feeds
`cosetWreath_not_isSofic_of_sequentialNormalization`.
-/

namespace GroupApproximation.CommutingSoficActions

open GroupApproximation.SurjunctiveNonsofic

/-- `Ambient` is sofic, because it is residually finite. -/
theorem ambient_isSofic : IsSofic Ambient := by
  haveI : Group.ResiduallyFinite Ambient := ambient_residuallyFinite
  exact isSofic_of_isLEF isLEF_of_residuallyFinite

/-- Kun–Thom Theorem 4.1 for the explicit pair. -/
theorem peripheral_hasSequentialCentralizerNormalization :
    HasSequentialCentralizerNormalization Peripheral :=
  hasSequentialCentralizerNormalization_of_kazhdan_infranormal
    ambient_hasKazhdanPropertyT peripheral_hasKazhdanPropertyT peripheral_isInfranormal

/-- **The Kun–Thom coset action is not sofic.** -/
theorem not_isSoficAction_ambient_quotient_peripheral :
    ¬ IsSoficAction Ambient (Ambient ⧸ Peripheral) := fun h =>
  cosetWreath_not_isSofic_of_sequentialNormalization
    peripheral_hasSequentialCentralizerNormalization
    (GeneralizedWreath.isSofic_wreath (isSofic_of_finite (Multiplicative (ZMod 2)))
      ambient_isSofic h)

end GroupApproximation.CommutingSoficActions
