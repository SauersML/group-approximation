---
rg: 2
id: kt-step-nine-hamming-for-transported-bisections
kind: claim
title: Transported bisections of a cluster frame give a vanishing step-9 Hamming distance, given estimate (7) and conjugation words
distinct_from:
  kt-step-nine-hamming-estimate-from-actual-defects: that node is the finite estimate and its sequential form, which take the retained objects, the budgets and the near bound as hypotheses. This node instantiates it over a cluster frame for transported bisections and supplies all of them.
  kt-step-nine-near-bound-from-counting-lift: that node is the near bound at one retained object. This node is the sequential Hamming estimate, which consumes that bound at every object covered by the lift.
artifacts:
  - GroupApproximation/KunThom/StepNineHammingProducerNear.lean
  - GroupApproximation/KunThom/StepNineHammingProducerSums.lean
  - GroupApproximation/KunThom/StepNineHammingProducerObjects.lean
  - GroupApproximation/KunThom/StepNineHammingProducer.lean
---

**Setting.** This is Kun–Thom, arXiv:2608.06222v3, the end of the proof of Theorem 4.1.
- `F` is a cluster frame over retained components of `A`, with vanishing threshold.
- `M` is `CountingEndgame.CompressorRelativeData t F`.
- `a` and `b` are sequences of total bisections of the cluster groupoid with
  `M.Transported a b`.
- `ws` are words of length at most `k` in the generators with
  `(ws s).map ι).prod = t · ι s · t⁻¹`.

Assume estimate (7) holds at every index `n` along the relative functor of `t`, for the
bridges realized by `A(t)⁻¹`, with an error `ε n X Z` of at most `3 · scale (F X)`.

**Proved.** `StepNineHammingProducer.vanishing_hammingDistance_patch_of_transported` gives

`Vanishing fun n ↦ d_H(patch b_n, A(t) · patch a_n · A(t)⁻¹)`.

This is the conclusion of the `hhamming` binder of
`CompressorNormalizationAssembly.seqNormalizes_distinguished_of_guardedSteps`.

## What a consumer must supply

* The words: `compressorWords`, `compressorWordBound`, `compressorWords_length_le` and
  `compressorWords_prod` of the normalized setup. The distinguished compressor is a
  compressor.
* Estimate (7) for `M`, with its error bound. `CompressorRelativeData` has no such
  field yet, so the binder cannot be discharged from this node alone.
