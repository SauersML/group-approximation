import GroupApproximation.BowenChapman.LaurentPairKazhdan
import GroupApproximation.BowenChapman.WreathWitness
import GroupApproximation.KunThom.NormalizationFromCriterion

/-!
# The coset wreath witness answers Bowen–Chapman Problem 1.1

Property (T) for `Ambient` and `Peripheral`, together with infranormality of
`Peripheral`, gives sequential centralizer normalization (Kun–Thom Theorem 4.1).
With `BowenChapman/WreathWitness` this makes the coset wreath product
`(ℤ/2ℤ) ≀_{G/Γ} G` a finitely generated surjunctive group that is not sofic.
-/

namespace GroupApproximation.BowenChapman

open GroupApproximation

/-- The coset wreath witness is not sofic. -/
theorem cosetWreath_not_isSofic : ¬ IsSofic CosetWreath :=
  cosetWreath_not_isSofic_of_sequentialNormalization
    (hasSequentialCentralizerNormalization_of_kazhdan_infranormal
      ambient_hasKazhdanPropertyT peripheral_hasKazhdanPropertyT
      peripheral_isInfranormal)

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
