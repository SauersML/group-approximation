/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BowenChapman.LaurentPairInfranormal
import GroupApproximation.BowenChapman.LaurentPairKazhdan
import GroupApproximation.BowenChapman.LaurentPairGeneration
import GroupApproximation.BowenChapman.LaurentPairResiduallyFinite
import GroupApproximation.KunThom.NormalizationFromCriterionConsumer
import GroupApproximation.Dynamics.DoubleFinitarySite
import GroupApproximation.Dynamics.DoubleConsequences
import GroupApproximation.Dynamics.SurjunctivityTransfer

/-!
# The Bowen–Chapman witness, given sequential normalization at the pair

The symmetric double `SymmetricDouble Ambient Peripheral` is finitely generated,
surjunctive and not sofic, provided sequential centralizer normalization holds
for `Peripheral ≤ Ambient`.  Every other input is a landed proof: finite
generation, countability, residual finiteness, non-normality, and surjunctivity
of doubles of surjunctive groups.

`GroupApproximation.BowenChapman.Endpoint` supplies the remaining hypothesis
from Kun–Thom, arXiv:2608.06222, Theorem 4.1, proved in `GroupApproximation.KunThom`.
-/

namespace GroupApproximation.BowenChapman

/-- **The Bowen–Chapman witness, given normalization.**  The symmetric double of
the explicit pair is finitely generated, surjunctive, and not sofic, once
sequential centralizer normalization holds for `Peripheral`. -/
theorem symmetricDouble_fg_surjunctive_not_isSofic_of_normalization
    (hnormalization : HasSequentialCentralizerNormalization Peripheral) :
    Group.FG (SymmetricDouble Ambient Peripheral) ∧
      Surjunctivity.IsSurjunctive (SymmetricDouble Ambient Peripheral) ∧
      ¬ IsSofic (SymmetricDouble Ambient Peripheral) := by
  haveI : Group.FG Ambient := ambient_fg
  haveI : Group.ResiduallyFinite Ambient := ambient_residuallyFinite
  refine ⟨symmetricDouble_finitelyGenerated Ambient Peripheral, ?_, ?_⟩
  · exact Surjunctivity.isSurjunctive_symmetricDouble Peripheral
      Surjunctivity.isSurjunctive_of_residuallyFinite
  · obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal peripheral_not_normal
    exact not_isSofic_symmetricDouble_of_sequentialNormalization Peripheral
      hnormalization (t := t) hγ hesc

end GroupApproximation.BowenChapman
