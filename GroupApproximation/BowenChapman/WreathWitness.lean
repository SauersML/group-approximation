import GroupApproximation.BowenChapman.LaurentPairGeneration
import GroupApproximation.BowenChapman.LaurentPairInfranormal
import GroupApproximation.BowenChapman.LaurentPairResiduallyFinite
import GroupApproximation.Dynamics.SurjunctivityTransfer
import GroupApproximation.Dynamics.WreathFinitarySite
import GroupApproximation.Sofic.InfranormalCompressionPair
import GroupApproximation.Sofic.TargetEquivalence
import GroupApproximation.Sofic.WreathCentralizerNormalizationSequential

/-!
# The coset wreath witness for Bowen–Chapman Problem 1.1

The coset wreath product `CosetWreath = (ℤ/2ℤ) ≀_{G/Γ} G` over the explicit pair
`Γ = Peripheral ≤ G = Ambient`.

* finitely generated (`cosetWreath_fg`): `Ambient` is finitely generated and acts
  transitively on its cosets;
* surjunctive (`cosetWreath_isSurjunctive`): `Ambient` is residually finite, hence
  surjunctive, and a wreath product with finite lamps over a surjunctive base is
  surjunctive;
* not sofic as soon as `Peripheral` has sequential centralizer normalization
  (`cosetWreath_not_isSofic_of_sequentialNormalization`), because non-normality of
  `Peripheral` supplies an escaping conjugate.

`BowenChapman/WreathWitnessEndpoint` supplies that normalization from property (T)
and infranormality.
-/

namespace GroupApproximation.BowenChapman

open GroupApproximation

/-- The coset wreath product `(ℤ/2ℤ) ≀_{G/Γ} G` over the explicit pair. -/
abbrev CosetWreath : Type :=
  Wreath (Multiplicative (ZMod 2)) Ambient (Ambient ⧸ Peripheral)

/-- The coset wreath witness is finitely generated. -/
theorem cosetWreath_fg : Group.FG CosetWreath :=
  wreath_quotient_fg Peripheral ambient_fg inferInstance

/-- The coset wreath witness is surjunctive. -/
theorem cosetWreath_isSurjunctive : Surjunctivity.IsSurjunctive CosetWreath := by
  haveI : Group.ResiduallyFinite Ambient := ambient_residuallyFinite
  exact Surjunctivity.isSurjunctive_wreath
    (isResiduallyFinite_of_finite (Multiplicative (ZMod 2)))
    Surjunctivity.isSurjunctive_of_residuallyFinite

/-- The coset wreath witness is not sofic once the peripheral subgroup has
sequential centralizer normalization. -/
theorem cosetWreath_not_isSofic_of_sequentialNormalization
    (hcentralizer : HasSequentialCentralizerNormalization Peripheral) :
    ¬ IsSofic CosetWreath := by
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal peripheral_not_normal
  exact not_isSofic_wreath_of_sequentialNormalization Peripheral hcentralizer hγ hesc

end GroupApproximation.BowenChapman
