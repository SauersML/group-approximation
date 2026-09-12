import GroupApproximation.BowenChapman.LaurentPairInfranormal
import GroupApproximation.BowenChapman.LaurentPairKazhdan
import GroupApproximation.BowenChapman.LaurentPairGeneration
import GroupApproximation.BowenChapman.LaurentPairResiduallyFinite
import GroupApproximation.KunThom.NormalizationFromCriterion
import GroupApproximation.Dynamics.WreathFinitarySite
import GroupApproximation.Dynamics.SurjunctivityTransfer
import GroupApproximation.Sofic.InfranormalCompressionPair
import GroupApproximation.Sofic.TargetEquivalence
import GroupApproximation.Sofic.WreathCentralizerNormalizationSequential

/-!
# The coset wreath witness for Bowen–Chapman Problem 1.1

The second witness for a finitely generated surjunctive group that is not
sofic: the coset wreath product `(ℤ/2ℤ) ≀_{G/Γ} G` over the explicit pair
`Γ = Peripheral ≤ G = Ambient`.

* finitely generated: `Ambient` is finitely generated and acts transitively on
  its cosets (`wreath_quotient_fg`);
* surjunctive: `Ambient` is residually finite, hence surjunctive, and a wreath
  product with residually finite lamps over a surjunctive base is surjunctive
  (`Surjunctivity.isSurjunctive_wreath`);
* not sofic: property (T) for both groups and infranormality give sequential
  centralizer normalization (Kun–Thom Theorem 4.1), non-normality gives an
  escaping conjugate, and `not_isSofic_wreath_of_sequentialNormalization`
  concludes.
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

/-- The coset wreath witness is not sofic. -/
theorem cosetWreath_not_isSofic : ¬ IsSofic CosetWreath := by
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal peripheral_not_normal
  exact not_isSofic_wreath_of_centralizerNormalization Peripheral
    (hasSoficCentralizerNormalization_of_kazhdan_infranormal
      ambient_hasKazhdanPropertyT peripheral_hasKazhdanPropertyT
      peripheral_isInfranormal)
    hγ hesc

/-- **The coset wreath witness answers Bowen–Chapman Problem 1.1.** -/
theorem cosetWreath_fg_surjunctive_not_isSofic :
    Group.FG CosetWreath ∧ Surjunctivity.IsSurjunctive CosetWreath ∧
      ¬ IsSofic CosetWreath :=
  ⟨cosetWreath_fg, cosetWreath_isSurjunctive, cosetWreath_not_isSofic⟩

/-- Existence form, through the coset wreath witness. -/
theorem exists_fg_surjunctive_not_isSofic_of_cosetWreath :
    ∃ (E : Type) (_ : Group E), Group.FG E ∧ Surjunctivity.IsSurjunctive E ∧
      ¬ IsSofic E :=
  ⟨CosetWreath, inferInstance, cosetWreath_fg_surjunctive_not_isSofic⟩

end GroupApproximation.BowenChapman
