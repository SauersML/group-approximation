/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BowenChapman.LaurentPair
import GroupApproximation.Kazhdan.Kazhdan
import GroupApproximation.Sofic.InfranormalCompressionPair
import GroupApproximation.KunThom.NormalizationFromCriterionConsumer

/-!
# The nonsoficity of the Bowen–Chapman witness from its leaves

The witness for Bowen–Chapman, arXiv:2511.06586, Problem 1.1, is the symmetric
double `SymmetricDouble Ambient Peripheral` of the explicit pair
`Peripheral ≤ Ambient` from `GroupApproximation.BowenChapman.LaurentPair`.

This module derives the nonsoficity of that double from five facts about the
pair and one general normalization theorem, each taken as an explicit
hypothesis:

* `Ambient` is countable;
* `Ambient` and `Peripheral` have property `(T)`;
* `Peripheral` is infranormal and not normal in `Ambient`;
* along every sofic approximation of a countable `(T)` group `G`, a sequence of
  permutations that asymptotically commutes with an infranormal `(T)` subgroup
  `Γ` still asymptotically commutes with `Γ` after conjugation by any element
  of `G` (Kun–Thom, arXiv:2608.06222, Theorem 4.1, in sequential form).

Each of the first five hypotheses has the type of a declaration in
`GroupApproximation.BowenChapman` that proves it.
`GroupApproximation.BowenChapman.EndpointOfNormalization` proves this conclusion,
together with finite generation and surjunctivity, with normalization at this
pair as its only hypothesis.
-/

namespace GroupApproximation.BowenChapman

/-- **Nonsoficity of the witness, from its leaves.**  Non-normality supplies a
compressor `t` and a mark `γ ∈ Peripheral` with `t⁻¹ γ t ∉ Peripheral`; the
normalization theorem at the pair supplies sequential centralizer
normalization; the double bridge then makes the symmetric double nonsofic. -/
theorem symmetricDouble_not_isSofic_of_leaves
    (hcount : Countable Ambient)
    (hTambient : HasKazhdanPropertyT.{0, 0} Ambient)
    (hTperipheral : HasKazhdanPropertyT.{0, 0} ↥Peripheral)
    (hinf : IsInfranormal Peripheral)
    (hnotNormal : ¬ Peripheral.Normal)
    (hnormalization : ∀ {G : Type} [Group G] [Countable G] {Γ : Subgroup G},
      HasKazhdanPropertyT.{0, 0} G → HasKazhdanPropertyT.{0, 0} ↥Γ →
        IsInfranormal Γ → HasSequentialCentralizerNormalization Γ) :
    ¬ IsSofic (SymmetricDouble Ambient Peripheral) := by
  haveI := hcount
  obtain ⟨t, γ, hγ, hesc⟩ := exists_escape_of_not_normal hnotNormal
  exact not_isSofic_symmetricDouble_of_sequentialNormalization Peripheral
    (hnormalization hTambient hTperipheral hinf) (t := t) hγ hesc

end GroupApproximation.BowenChapman
