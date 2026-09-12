import GroupApproximation.KunThom.RelativeFunctorImproveEstimate
import GroupApproximation.KunThom.CountingEndgameProps

/-!
# The relative data of a compressor over a cluster frame

`seqNormalizes_distinguished_of_guardedSteps` asks, in `hfunctor`, for relative data
`CountingEndgame.CompressorRelativeData t F` over every cluster frame whose threshold
dominates the matching error.  `exists_compressorRelativeData_of_good` packages them from
a retained domain `dom q n`, a matching `π q n` injective on it, and a family `good q n`
of objects on which the pointwise bounds of
`RelativeFunctorImprove.frameRelativeFunctorOfGood` hold.

* The matched objects of `q` are `dom q n ∩ good q n`, and the retained objects their
  image under `π q n`.
* The functor of `q` is `frameRelativeFunctorOfGood` with the words `ws q`, and the size
  bound comes from `frame_size_le_of_good`.
* Estimate (7) for `t` comes from `frameRelativeFunctorOfGood_estimate` and
  `frameEstimateError_le_of_good`.
* The negligible unmatched and unretained weights, the missing bridge mass along `π` on
  `dom`, and the self-bridge mass of the generators are hypotheses.  The missing bridge
  mass on the matched objects follows from the one on `dom`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

open Classical
open RelativeFunctorImprove

/-- **Relative data from a good family.**  Given a setup containing `t`, an ambient
expander decomposition, words for the conjugated generators with the repair-factor bound,
and a retained domain, a matching and a good family satisfying the pointwise bounds of
`frameRelativeFunctorOfGood` and the negligibility hypotheses, some relative data of `t`
over `F` exist. -/
theorem exists_compressorRelativeData_of_good {G : Type} [Group G] {A : SoficApproximation G}
    {K : Type} [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R)
    (setup : CompressionSetup G K PUnit.{1}) {t : G} (ht : t ∈ setup.compressors)
    (ambient : ExpanderDecomposition A setup.ambientGenerators)
    (hself : ∀ s ∈ setup.generatorsΓ, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ i, (((F.embedding n).bridge (A.map n (setup.embedΓ s)) i i).sourceDefect : ℝ))
    (ws : G → ↥R.data.generators → List ↥R.data.generators) {k : ℕ}
    (hk : ∀ q s, (ws q s).length ≤ k)
    (hK₀ : 2 * (1 + (Fintype.card ↥R.data.generators : ℝ) * k) ≤ F.repairFactor)
    (dom good : G → ∀ n, Finset (F.Obj n)) (π : G → ∀ n, F.Obj n → F.Obj n)
    (hπ : ∀ q ∈ setup.compressors, ∀ n, Set.InjOn (π q n) (dom q n : Set (F.Obj n)))
    (hbridge : ∀ q n, ∀ i ∈ good q n,
      100 * (((F.embedding n).bridge (A.map n q) i (π q n i)).sourceDefect +
        ((F.embedding n).bridge (A.map n q) i (π q n i)).targetDefect) ≤
        (F.system n).scale (π q n i))
    (herr : ∀ q n, ∀ i ∈ good q n,
      40 * ((inError (F.embedding n) (F.action n) (A.map n q)⁻¹ (ws q) (π q n i) i +
        outError (F.embedding n) (F.action n) (A.map n q)⁻¹ (ws q) (π q n i) i : ℕ) : ℝ) ≤
        F.threshold n * (F.system n).scale (π q n i))
    (hscale : ∀ q n, ∀ i ∈ good q n, 400 ≤ (F.system n).scale (π q n i))
    (hunmatched : ∀ q ∈ setup.compressors,
      Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
        ∑ i ∈ Finset.univ \ (dom q n ∩ good q n), (Fintype.card ((F.embedding n).model i) : ℝ))
    (hunretained : ∀ q ∈ setup.compressors,
      Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
        ∑ i ∈ Finset.univ \ (dom q n ∩ good q n).image (π q n),
          (Fintype.card ((F.embedding n).model i) : ℝ))
    (hbridgeDom : ∀ q ∈ setup.compressors,
      Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
        ∑ i ∈ dom q n, (((F.embedding n).bridge (A.map n q) i (π q n i)).sourceDefect : ℝ)) :
    Nonempty (CountingEndgame.CompressorRelativeData t F) :=
  ⟨{ setup := setup
     mem_compressors := ht
     ambientGenerators := setup.ambientGenerators
     ambient := ambient
     ambientGenerators_symm := setup.ambientGenerators_symmetric
     ambientGenerators_generate := setup.ambientGenerators_generate
     bridge_self_negligible := hself
     matched := fun q n ↦ dom q n ∩ good q n
     retained := fun q n ↦ (dom q n ∩ good q n).image (π q n)
     functor := fun q hq n ↦ frameRelativeFunctorOfGood F n q (ws q) (hk q) hK₀ (dom q n)
       (good q n) (π q n) (hπ q hq n) (hbridge q n) (herr q n) (hscale q n)
     unmatched_negligible := hunmatched
     unretained_negligible := hunretained
     bridge_negligible := fun q hq ↦ Negligible.mono_nonneg (fun _ ↦ Nat.cast_nonneg _)
       (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
       (fun _ ↦ Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
         fun _ _ _ ↦ Nat.cast_nonneg _) (hbridgeDom q hq)
     size_le := fun q _ n ↦ frame_size_le_of_good F n q (dom q n) (good q n) (π q n)
       (hbridge q n)
     estimateError := fun n ↦ frameEstimateError F n (π t n)
       (finsetSurjOn_image (π t n) (dom t n ∩ good t n))
     estimate := fun n {_X _Z} c θ hθ ↦ frameRelativeFunctorOfGood_estimate F n t (ws t) (hk t)
       hK₀ (dom t n) (good t n) (π t n) (hπ t ht n) (hbridge t n) (herr t n) (hscale t n)
       c θ hθ
     estimateError_le := fun n X Z ↦ frameEstimateError_le_of_good F n t (ws t) (hk t) hK₀
       (dom t n) (good t n) (π t n) (hπ t ht n) (hbridge t n) (herr t n) (hscale t n) X Z }⟩

end CompressorNormalizationAssembly
end GroupApproximation
