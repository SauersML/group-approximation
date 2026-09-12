---
rg: 2
id: kt-per-compressor-assembly-over-cluster-frames
kind: claim
title: The Lean assembly of Kun--Thom 4.1 proves its sequential form for infranormal Kazhdan pairs
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Theorem 4.1 itself, in the universal sofic group and imported by citation; this is the Lean derivation of its sequential form, over sofic approximations and sequences of permutations.
  kt-counting-props-producers: that proves three hypotheses of this assembly from the relative data; this is the assembly that consumes them together with frames, the joint scale choice, decompositions, words and the other producers.
artifacts:
  - GroupApproximation/KunThom/CompressorNormalizationAssembly.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyFrame.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyThreshold.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyFrameSteps.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyDecomposition.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyWords.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyCore.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyRelativeData.lean
  - GroupApproximation/KunThom/CompressorNormalizationCore.lean
---

**ESTABLISHED in Lean.** This is Kun--Thom, arXiv:2608.06222v3, Theorem 4.1, in sequential
form, proved with no literature hypotheses.

**Statement.** Let `G` be a countable group and `Γ` an infranormal subgroup, with both `G`
and `Γ` having property `(T)`. Then
`hasSequentialCentralizerNormalization_of_kazhdan_infranormal` proves
`HasSequentialCentralizerNormalization Γ`. For every sofic approximation `A` of `G` and every
sequence `v` of permutations that almost commutes with `A(γ)` for all `γ ∈ Γ`, the sequence
`A(g) v A(g)⁻¹` almost commutes with `A(γ)` for all `g ∈ G` and `γ ∈ Γ`.

The per-compressor core is `seqNormalizes_distinguished_of_kazhdan`. It gives
`SeqNormalizes Γ C.distinguished` for every criterion setup `C` whose embedding is the
inclusion. `hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core`
(`KunThom/NormalizationProducer`) spreads it to all of `G`.

**The assembly.** `seqNormalizes_of_compressor_of_steps` argues by contradiction along a
subsequence, and it runs over cluster frames (`seqNormalizes_of_compressor_of_frameSteps`).
Its hypotheses are discharged as follows.
- `hframe`: the joint scale choice `exists_clusterFrame`, which prescribes `√ρ` and so gets
  `ρ = o(threshold)`.
- `hconv`: `ClusterFrame.almostCommutes_patch`.
- `hdecomp`, `hkazhdan`, `hdefect`: from property `(T)` (`exists_compressorDecomposition`,
  `exists_kazhdanPair_retained`, `generatorDefect_vanishing`).
- `hrep`: `ClusterFrame.exists_bis_patch_close_of_retained`, the forward half of
  Lemma 4.2(4).
- `hmatching`: `RelativeDataMarkov.matchingError`, with `matchingError_nonneg` and
  `matchingError_vanishing`.
- `hfunctor`: `exists_compressorRelativeData_of_good`. It uses the retained domain and
  matching of every compressor, the good objects of `RelativeDataGood` (Markov deletion
  at a vanishing threshold), `frameRelativeFunctorOfGood`, and estimate (7) from
  `RelativeFunctorImproveEstimate`.
- `honesided`, `hmedian`, `hcounting`: the producers of `kt-counting-props-producers`.
- `hhamming`: `StepNineHammingProducer.vanishing_hammingDistance_patch_of_transported`, with
  `compressorWords` and the estimate fields of the relative data.

**Defects found and repaired along the way.**
- *`hhamming` is false over relative data without estimate (7).* The field `functor`
  recorded only a matching, a faithful morphism and `obj_π`. Twisting the functor by
  automorphisms of the matched objects keeps every field, but then the lift of `Transported`
  approximates a twisted conjugate. `CompressorRelativeData` now carries `estimate`,
  `estimateError` and `estimateError_le` for the distinguished compressor.
- *`hhamming` needs the frame guards.* At a frame with constant threshold `h`, arrow
  defects of order `h · scale` put the step-9 budget at order `h |Y|`. So the hypothesis is
  required only at frames with the setup's repair factor and a vanishing threshold
  (`seqNormalizes_distinguished_of_guardedSteps`).
- *Per-object scales.* A partial cluster system with one uniform scale cannot carry the
  representation of almost centralizers. The frame uses per-object scales `|C| / 18`, with
  pair scales the minimum.
- *Repair factor.* Factor `4` does not survive transport through words for `q s q⁻¹`, so the
  factor is `compressorRepairFactor = 2 (1 + |S| k) + 4`.
- *Coerced words.* `compressorWords_prod` reads a word through the list coercion, so
  consumers bridge it with `RelativeDataMarkov.prod_map_bind_coe`.

Derivation: `kt-per-compressor-assembly-over-cluster-frames-proof`.
