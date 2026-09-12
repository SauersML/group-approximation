/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BowenChapman.EndpointOfInputs
import GroupApproximation.BowenChapman.LaurentPairInfranormal
import GroupApproximation.BowenChapman.LaurentPairKazhdan
import GroupApproximation.BowenChapman.LaurentPairGeneration
import GroupApproximation.BowenChapman.LaurentPairResiduallyFinite
import GroupApproximation.KunThom.CentralizerNormalization
import GroupApproximation.Dynamics.DoubleFinitarySite
import GroupApproximation.Dynamics.DoubleConsequences
import GroupApproximation.Dynamics.SurjunctivityTransfer

/-!
# A finitely generated surjunctive group that is not sofic

Gromov and Weiss proved that sofic groups are surjunctive.  Bowen and Chapman,
arXiv:2511.06586, Problem 1.1, ask for the converse: are all surjunctive groups
sofic?  The theorems below answer no.

The witness is the symmetric double `G *_Γ G` of the pair

```text
Γ = EL₃(𝔽₂[x₁, x₂, x₃])  ≤  G = EL₃(𝔽₂[x₁^±¹, x₂^±¹, x₃^±¹]) ⋊ EL₃(ℤ),
```

with `EL₃(ℤ)` acting by monomial substitution.

* **Finitely generated.**  `G` is finitely generated, and the two copies of a
  finite generating set generate the double.
* **Surjunctive.**  `G` is residually finite, hence surjunctive, and a double
  of a surjunctive group is surjunctive.
* **Not sofic.**  `G` and `Γ` have property `(T)`, and `Γ` is infranormal but
  not normal, so centralizers of `Γ` in permutation ultraproducts are
  normalized by `G`, which makes the double nonsofic.
-/

namespace GroupApproximation.BowenChapman

/-- **The Bowen–Chapman witness.**  The symmetric double of the explicit pair
is finitely generated, surjunctive, and not sofic. -/
theorem symmetricDouble_fg_surjunctive_not_isSofic :
    Group.FG (SymmetricDouble Ambient Peripheral) ∧
      Surjunctivity.IsSurjunctive (SymmetricDouble Ambient Peripheral) ∧
      ¬ IsSofic (SymmetricDouble Ambient Peripheral) := by
  haveI : Group.FG Ambient := ambient_fg
  haveI : Group.ResiduallyFinite Ambient := ambient_residuallyFinite
  refine ⟨symmetricDouble_finitelyGenerated Ambient Peripheral, ?_, ?_⟩
  · exact Surjunctivity.isSurjunctive_symmetricDouble Peripheral
      Surjunctivity.isSurjunctive_of_residuallyFinite
  · exact symmetricDouble_not_isSofic_of_leaves inferInstance
      ambient_hasKazhdanPropertyT peripheral_hasKazhdanPropertyT
      peripheral_isInfranormal peripheral_not_normal
      hasSoficCentralizerNormalization_of_kazhdan_infranormal

/-- **Bowen–Chapman, Problem 1.1, answered negatively.**  Some finitely
generated group is surjunctive and not sofic. -/
theorem exists_fg_surjunctive_not_isSofic :
    ∃ (E : Type) (_ : Group E),
      Group.FG E ∧ Surjunctivity.IsSurjunctive E ∧ ¬ IsSofic E :=
  ⟨SymmetricDouble Ambient Peripheral, inferInstance,
    symmetricDouble_fg_surjunctive_not_isSofic⟩

end GroupApproximation.BowenChapman
