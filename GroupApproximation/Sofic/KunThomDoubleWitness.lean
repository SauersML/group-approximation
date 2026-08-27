import GroupApproximation.Sofic.MFNonsoficDoubleEndpoint
import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Sofic.ScalingFamilyLinearWitness

/-!
# The combinatorial half of the Kun--Thom--Shulman datum, discharged

`Sofic.MFNonsoficDoubleEndpoint.KunThomShulmanDoubleData` has six fields and
is listed in `metadata/LITERATURE_QUARANTINE.md` as one citation, "the
Kun--Thom/Shulman double construction".  It is not one citation.  Four of the
six fields are combinatorics this repository already proves, and the two that
remain are *two different papers*:

* `operatorMF` --- Shulman's symmetric-amalgamation theorem;
* `centralizerNormalization` --- Kun--Thom's centralizer rigidity in a
  permutation ultraproduct.

The other four --- the compressor `t`, the element `γ` of the peripheral
subgroup, its membership, and the escape `t⁻¹γt ∉ Γ` --- are exactly the
marked-compression data.  `MarkedCompression.tVertical_inv_conj_not_mem`
proves the escape for the vertical group of any injective compression `α`,
for any `a₀` off the range of `α`, and
`ScalingFamilyLinearWitness.v1G_not_mem_range_alphaScale` supplies such an
`a₀` for every member of the scaling family.  So at the repository's own
compression pair the combinatorial half of the datum is discharged outright.

* `compressedCopy` --- the peripheral subgroup `ι(Γ) ≤ Vertical`;
* `dataOfInputs` --- the datum, from the two literature conclusions alone;
* `scalingData` --- the same at the `m`-th member of the scaling family, where
  even the choice of `a₀` is discharged;
* `conclusion_of_inputs` --- the endpoint those two conclusions buy.

## Manuscript status

Splits the Kun--Thom row of `metadata/LITERATURE_QUARANTINE.md` into its two
genuine citations and discharges everything else in it.
-/

namespace GroupApproximation
namespace KunThomDoubleWitness

open MarkedCompression

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The compressed copy of `Γ` inside the vertical group --- the peripheral
subgroup the double is taken over. -/
abbrev compressedCopy : Subgroup (Vertical α hα) :=
  (iotaVertical α hα).range

include hα in
/-- **The escape clause, proved.**  Conjugating a marked element by the
compressor moves it out of the compressed copy. -/
theorem escapes_of_not_mem_range {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    (tVertical α hα)⁻¹ * iotaVertical α hα a₀ * tVertical α hα
      ∉ compressedCopy α hα :=
  tVertical_inv_conj_not_mem α hα ha₀

/-- **The datum, from the two literature conclusions alone.**  Every other
field is proved here. -/
def dataOfInputs {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α)
    (hMF : IsGroupTheoreticMF
      (SymmetricDouble (Vertical α hα) (compressedCopy α hα)))
    (hcent : HasSoficCentralizerNormalization (compressedCopy α hα)) :
    KunThomShulmanDoubleData (Vertical α hα) (compressedCopy α hα) where
  operatorMF := hMF
  centralizerNormalization := hcent
  t := tVertical α hα
  γ := iotaVertical α hα a₀
  γ_mem := ⟨a₀, rfl⟩
  escapes := escapes_of_not_mem_range α hα ha₀

/-- The endpoint the two conclusions buy: the double is MF and nonsofic. -/
theorem conclusion_of_inputs [Countable (Vertical α hα)]
    {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α)
    (hMF : IsGroupTheoreticMF
      (SymmetricDouble (Vertical α hα) (compressedCopy α hα)))
    (hcent : HasSoficCentralizerNormalization (compressedCopy α hα)) :
    IsGroupTheoreticMF (SymmetricDouble (Vertical α hα) (compressedCopy α hα))
      ∧ ¬ IsSofic (SymmetricDouble (Vertical α hα) (compressedCopy α hα)) :=
  (dataOfInputs α hα ha₀ hMF hcent).conclusion

/-! ## At the scaling family, the choice of `a₀` is discharged too -/

section Scaling

open ScalingFamilyLinearWitness

variable {m : ℕ}

/-- **The datum at the `m`-th member of the scaling family.**  Nothing is left
but Shulman's conclusion and Kun--Thom's. -/
def scalingData (hm : 2 ≤ m)
    (hMF : IsGroupTheoreticMF (SymmetricDouble
      (Vertical (alphaScale hm) (alphaScale_injective hm))
      (compressedCopy (alphaScale hm) (alphaScale_injective hm))))
    (hcent : HasSoficCentralizerNormalization
      (compressedCopy (alphaScale hm) (alphaScale_injective hm))) :
    KunThomShulmanDoubleData
      (Vertical (alphaScale hm) (alphaScale_injective hm))
      (compressedCopy (alphaScale hm) (alphaScale_injective hm)) :=
  dataOfInputs (alphaScale hm) (alphaScale_injective hm)
    (v1G_not_mem_range_alphaScale hm) hMF hcent

end Scaling

end KunThomDoubleWitness
end GroupApproximation
