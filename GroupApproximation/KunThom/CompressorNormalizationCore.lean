import GroupApproximation.KunThom.CompressorNormalizationAssemblyCore
import GroupApproximation.KunThom.CompressorNormalizationAssemblyRelativeData
import GroupApproximation.KunThom.CentralizerBisectionRepresentationFrameRetained
import GroupApproximation.KunThom.StepNineHammingProducer
import GroupApproximation.KunThom.RelativeDataGood
import GroupApproximation.KunThom.RelativeDataErrorsVanishing
import GroupApproximation.KunThom.NormalizationProducer

/-!
# Kun--Thom Theorem 4.1, sequential form

`seqNormalizes_distinguished_of_kazhdan_of_functor` instantiates
`CompressorNormalizationAssembly.seqNormalizes_distinguished_of_guardedSteps` with:
* `hrep`: `ClusterFrame.exists_bis_patch_close_of_retained`, the forward half of
  Lemma 4.2(4);
* `hhamming`: `StepNineHammingProducer.vanishing_hammingDistance_patch_of_transported`, with
  the words `compressorWords` and the estimate (7) fields of the relative data.

`seqNormalizes_distinguished_of_kazhdan` is the per-compressor core consumed by
`hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core`.  It discharges the
remaining inputs:
* the matching error `RelativeDataMarkov.matchingError`, nonnegative and vanishing;
* `hfunctor`: `exists_compressorRelativeData_of_good` on the retained domain and matching
  of every compressor, with the good objects of `RelativeDataGood`.

`hasSequentialCentralizerNormalization_of_kazhdan_infranormal` is Kun--Thom Theorem 4.1 in
the sequential form of `HasSequentialCentralizerNormalization`.
-/

namespace GroupApproximation

open CompressorNormalizationAssembly

/-- **The per-compressor core of Kun--Thom Theorem 4.1, given relative data.**  For a
countable Kazhdan group `G`, an infinite Kazhdan subgroup `Γ` and a criterion setup of `Γ`
whose embedding is the inclusion, the distinguished compressor normalizes sequential
almost-centralizers of `Γ`, once relative data exist over every frame whose threshold
dominates a vanishing matching error. -/
theorem seqNormalizes_distinguished_of_kazhdan_of_functor
    {G : Type} [Group G] [Countable G] {Γ : Subgroup G} [Infinite ↥Γ]
    (hG : HasKazhdanPropertyT.{0, 0} G) (hΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (C : CompressionSetup G ↥Γ PUnit.{1}) (hembed : ∀ g : ↥Γ, C.embedΓ g = (g : G))
    (matchingError : ∀ {A : SoficApproximation G},
      CompressorDecomposition (normalizedSetup C hembed) A → ℕ → ℝ)
    (hmatching : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A),
        (∀ n, 0 ≤ matchingError D n) ∧ Vanishing (matchingError D))
    (hfunctor : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A) (F : ClusterFrame D.retained),
        F.repairFactor = compressorRepairFactor (normalizedSetup C hembed) →
          Vanishing F.threshold →
            (Vanishing fun n ↦ matchingError D n / F.threshold n) →
              Nonempty (CountingEndgame.CompressorRelativeData C.distinguished F)) :
    SeqNormalizes Γ C.distinguished :=
  seqNormalizes_distinguished_of_guardedSteps hG hΓ C hembed matchingError hmatching
    (fun _ _ F _ hthr v _ hdom ↦ F.exists_bis_patch_close_of_retained hthr v hdom) hfunctor
    (fun _ _ F _ hthr M a b htr ↦
      StepNineHammingProducer.vanishing_hammingDistance_patch_of_transported F hthr
        C.distinguished M (compressorWords (normalizedSetup C hembed) C.distinguished)
        (compressorWordBound (normalizedSetup C hembed))
        (compressorWords_length_le (normalizedSetup C hembed) C.distinguished)
        (fun s ↦ (RelativeDataMarkov.prod_map_bind_coe (normalizedSetup C hembed).generatorsΓ
            (normalizedSetup C hembed).embedΓ
            (compressorWords (normalizedSetup C hembed) C.distinguished s)).symm.trans
          (compressorWords_prod (normalizedSetup C hembed) C.distinguished_mem s))
        M.estimateError M.estimate M.estimateError_le a b htr)

/-- **The per-compressor core of Kun--Thom Theorem 4.1.**  For a countable Kazhdan group
`G`, a Kazhdan subgroup `Γ` and a criterion setup of `Γ` whose embedding is the inclusion,
the distinguished compressor normalizes sequential almost-centralizers of `Γ`. -/
theorem seqNormalizes_distinguished_of_kazhdan
    {G : Type} [Group G] [Countable G] {Γ : Subgroup G}
    (hG : HasKazhdanPropertyT.{0, 0} G) (hΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (C : CompressionSetup G ↥Γ PUnit.{1})
    (hembed : ∀ g : ↥Γ, C.embedΓ g = (g : G)) :
    SeqNormalizes Γ C.distinguished := by
  haveI : Infinite ↥Γ := C.infiniteΓ
  exact seqNormalizes_distinguished_of_kazhdan_of_functor hG hΓ C hembed
    (fun D ↦ RelativeDataMarkov.matchingError D)
    (fun _ D ↦ ⟨RelativeDataMarkov.matchingError_nonneg D,
      RelativeDataMarkov.matchingError_vanishing D⟩)
    (fun _ D F hK _ hdens ↦ exists_compressorRelativeData_of_good F (normalizedSetup C hembed)
      C.distinguished_mem D.ambient (ClusterFrame.matchingGeneratorBridge_negligible D F)
      (compressorWords (normalizedSetup C hembed))
      (compressorWords_length_le (normalizedSetup C hembed))
      ((two_mul_le_compressorRepairFactor (normalizedSetup C hembed)).trans hK.symm.le)
      (fun q n ↦ D.toLocal.compressorDomains (ClusterFrame.matchingParent D F) q n)
      (RelativeDataMarkov.goodObjects D F)
      (fun q n ↦ D.toLocal.compressorMatch (ClusterFrame.matchingParent D F) q n)
      (fun _ hq n ↦ RelativeDataMarkov.matchInjOn D F hq n)
      (RelativeDataMarkov.goodObjects_hbridge D F) (RelativeDataMarkov.goodObjects_herr D F)
      (RelativeDataMarkov.goodObjects_hscale D F)
      (fun _ hq ↦ RelativeDataMarkov.matchedObjects_unmatched_negligible D F hq hdens)
      (fun _ hq ↦ RelativeDataMarkov.matchedObjects_unretained_negligible D F hq hdens)
      (fun q hq ↦ ClusterFrame.matchingBridge_negligible D F q hq))

/-- **Kun--Thom Theorem 4.1, sequential form.**  If `Γ` is an infranormal subgroup of a
countable group `G`, and both have property `(T)`, then every element of `G` carries
sequential almost-centralizers of `Γ` to almost-centralizers of `Γ`, in every sofic
approximation of `G`. -/
theorem hasSequentialCentralizerNormalization_of_kazhdan_infranormal
    {G : Type} [Group G] [Countable G] {Γ : Subgroup G}
    (hG : HasKazhdanPropertyT.{0, 0} G) (hΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (hinf : IsInfranormal Γ) : HasSequentialCentralizerNormalization Γ :=
  hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core hG hΓ hinf
    fun C hembed ↦ seqNormalizes_distinguished_of_kazhdan hG hΓ C hembed

end GroupApproximation
