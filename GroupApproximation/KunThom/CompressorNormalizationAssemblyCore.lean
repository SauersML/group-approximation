import GroupApproximation.KunThom.CompressorNormalizationAssemblyDecomposition
import GroupApproximation.KunThom.CompressorNormalizationAssemblyWords
import GroupApproximation.KunThom.CountingEndgamePropsMedian
import GroupApproximation.KunThom.CountingEndgamePropsCounting

/-!
# The per-compressor core over concrete data

`seqNormalizes_of_compressor_of_frameSteps` runs over abstract decomposition and
relative data.  This module instantiates it for a compression setup `C` of `Γ`
whose embedding is the inclusion, which is the shape of the core consumed by
`hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core`.

* `normalizedSetup C hembed`: the setup `C` with its embedding replaced by
  `Γ.subtype`, which it agrees with pointwise.  The compressors, the distinguished
  compressor and the generators do not change.
* Decompositions are `CompressorDecomposition` over the normalized setup, retained
  components are `CompressorDecomposition.retained`, the repair factor is
  `compressorRepairFactor`, and the generator defect is `generatorDefect`.
  `hdecomp`, `hkazhdan` and `hdefect` are discharged by
  `exists_compressorDecomposition`, `exists_kazhdanPair_retained` with
  `four_le_compressorRepairFactor`, and `generatorDefect_vanishing`.
* Relative data are `CountingEndgame.CompressorRelativeData`, with its Props
  `OneSided`, `Concentrated` and `Transported`.  `honesided`, `hmedian` and `hcounting`
  are discharged by `CountingEndgame.CompressorRelativeData.oneSided`,
  `CountingEndgame.CompressorRelativeData.concentrated_of_oneSided` and
  `CountingEndgame.CompressorRelativeData.transported`.

`seqNormalizes_distinguished_of_steps` is the result.  Its open hypotheses are the
matching error and `hmatching`, `hrep`, `hfunctor` and `hhamming`, all stated over
these concrete types.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

/-- The setup `C` with its embedding replaced by the inclusion of `Γ`. -/
def normalizedSetup {G : Type} [Group G] {Γ : Subgroup G} (C : CompressionSetup G ↥Γ PUnit.{1})
    (hembed : ∀ g : ↥Γ, C.embedΓ g = (g : G)) : CompressionSetup G ↥Γ PUnit.{1} where
  embedΓ := Γ.subtype
  embedΓ_injective := Γ.subtype_injective
  embedJ := C.embedJ
  embedJ_injective := C.embedJ_injective
  generatorsΓ := C.generatorsΓ
  generatorsΓ_one := C.generatorsΓ_one
  generatorsΓ_symmetric := C.generatorsΓ_symmetric
  generatorsΓ_generate := C.generatorsΓ_generate
  generatorsJ := C.generatorsJ
  generatorsJ_generate := C.generatorsJ_generate
  infiniteΓ := C.infiniteΓ
  compressors := C.compressors
  distinguished := C.distinguished
  distinguished_mem := C.distinguished_mem
  compressedEnd := C.compressedEnd
  compressedEnd_spec q hq g := by
    show ((C.compressedEnd q hq g : ↥Γ) : G) = q * (g : G) * q⁻¹
    rw [← hembed, ← hembed]
    exact C.compressedEnd_spec q hq g
  generates := by
    have hrange : Set.range Γ.subtype = Set.range C.embedΓ := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, hembed g⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g, (hembed g).symm⟩
    rw [hrange]
    exact C.generates
  centralizes g j := by
    have h := C.centralizes g j
    rw [hembed, hembed] at h
    exact h
  disjoint g j h := C.disjoint g j (by
    rw [hembed, hembed]
    exact h)

/-- **The forward inclusion for the distinguished compressor, over concrete data.** -/
theorem seqNormalizes_distinguished_of_steps {G : Type} [Group G] [Countable G]
    {Γ : Subgroup G} [Infinite ↥Γ]
    (hTG : HasKazhdanPropertyT.{0, 0} G) (hTΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (C : CompressionSetup G ↥Γ PUnit.{1}) (hembed : ∀ g : ↥Γ, C.embedΓ g = (g : G))
    (matchingError : ∀ {A : SoficApproximation G},
      CompressorDecomposition (normalizedSetup C hembed) A → ℕ → ℝ)
    (hmatching : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A),
        (∀ n, 0 ≤ matchingError D n) ∧ Vanishing (matchingError D))
    (hrep : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A) (F : ClusterFrame D.retained),
        F.repairFactor = compressorRepairFactor (normalizedSetup C hembed) →
          Vanishing F.threshold → ∀ v : ∀ n, Equiv.Perm (A.model n),
            (∀ γ ∈ Γ, A.AlmostCommutes v γ) →
              (Vanishing fun n ↦ generatorDefect D.retained v n / F.threshold n) →
                ∃ a : ∀ n, F.Bis n,
                  Vanishing fun n ↦ hammingDistance (A.model n) (v n) (F.patch n (a n)))
    (hfunctor : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A) (F : ClusterFrame D.retained),
        F.repairFactor = compressorRepairFactor (normalizedSetup C hembed) →
          Vanishing F.threshold →
            (Vanishing fun n ↦ matchingError D n / F.threshold n) →
              Nonempty (CountingEndgame.CompressorRelativeData C.distinguished F))
    (hhamming : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A) (F : ClusterFrame D.retained)
      (M : CountingEndgame.CompressorRelativeData C.distinguished F) (a b : ∀ n, F.Bis n),
        M.Transported a b →
          Vanishing fun n ↦ hammingDistance (A.model n) (F.patch n (b n))
            (A.map n C.distinguished * F.patch n (a n) * (A.map n C.distinguished)⁻¹)) :
    SeqNormalizes Γ C.distinguished :=
  seqNormalizes_of_compressor_of_frameSteps
    (Decomp := CompressorDecomposition (normalizedSetup C hembed))
    (retained := fun D ↦ D.retained)
    (repairFactor := fun _ ↦ compressorRepairFactor (normalizedSetup C hembed))
    (generatorDefect := fun D v n ↦ generatorDefect D.retained v n)
    (matchingError := matchingError)
    (Rel := fun F ↦ CountingEndgame.CompressorRelativeData C.distinguished F)
    (OneSided := fun M ↦ M.OneSided) (Concentrated := fun M ↦ M.Concentrated)
    (Transported := fun M a b ↦ M.Transported a b)
    (fun A ↦ exists_compressorDecomposition hTG hTΓ (normalizedSetup C hembed) A)
    (fun _ D ↦ ⟨four_le_compressorRepairFactor _,
      exists_kazhdanPair_retained hTΓ D.retained (normalizedSetup C hembed).generatorsΓ_symmetric⟩)
    (fun _ D v hv ↦ generatorDefect_vanishing D.retained v fun s _ ↦ hv (s : G) s.2)
    hmatching hrep hfunctor (fun _ _ _ M ↦ M.oneSided) (fun _ _ _ M h ↦ M.concentrated_of_oneSided h)
    (fun _ _ _ M h a ↦ M.transported h a) hhamming

end CompressorNormalizationAssembly
end GroupApproximation
