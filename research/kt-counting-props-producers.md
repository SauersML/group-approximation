---
rg: 2
id: kt-counting-props-producers
kind: claim
title: One-sided, concentration and transport producers of the Kun--Thom 4.1 per-compressor assembly
distinct_from:
  kt-counting-endgame-bisection-lift: that is the finite lift of a bisection through a faithful functor at one index; this defines the concrete relative data and Props of the per-compressor assembly and proves three of its hypotheses along the sofic approximation.
  kun-thom-sofic-centralizer-normalization: that is Theorem 4.1 itself, imported by citation; this proves three hypotheses of the Lean assembly of its proof from the relative data, and does not derive the theorem.
  kt-relative-cluster-functor-assembly: that builds and proves faithful the relative cluster functor; this takes its bundle as a field of the relative data and counts through it.
artifacts:
  - GroupApproximation/KunThom/CountingEndgameProps.lean
  - GroupApproximation/KunThom/CountingEndgamePropsScale.lean
  - GroupApproximation/KunThom/CountingEndgamePropsMedian.lean
  - GroupApproximation/KunThom/CountingEndgamePropsOneSided.lean
  - GroupApproximation/KunThom/CountingEndgamePropsSelect.lean
  - GroupApproximation/KunThom/CountingEndgamePropsCounting.lean
---

**ESTABLISHED in Lean.** The per-compressor assembly
`CompressorNormalizationAssembly.seqNormalizes_of_compressor_of_frameSteps` takes
relative data `Rel F` over cluster frames and three Props about it. This node fixes
all four and proves three of the hypotheses about them. Namespace
`GroupApproximation.CountingEndgame`.

**The data.** `CompressorRelativeData t F` carries the following.
- A compression setup with `t` among its compressors, and an ambient expander
  decomposition.
- The self-bridge bound of the generators of `Γ`.
- For every compressor `q`:
  - the matched objects `matched q n` and the retained objects `retained q n`;
  - the bundled relative cluster functor between them (Kun–Thom, Lemma 4.3);
  - negligible unmatched weight, unretained weight and missing bridge mass;
  - matched objects at most twice the size of their matches.

The matched family is the one retained domain. Nothing below deletes from it.

**The Props.**
- `OneSided`: `f (π q n i) ≤ (1 + κ q n) f i` off a family `Bad q n` of negligible
  weight, for the arrow count `f`. These are exactly the inputs `hκ`, `hκv`, `hone`
  and `hbad` of `MedianVertexForm.blockRatio_negligible`.
- `Concentrated`: the conclusion of `blockRatio_negligible` at `t`.
- `Transported a b`: a set of retained objects whose complement has negligible
  weight, at each of which `b n` carries the inclusion of a preimage of the
  transported arrow of `a n`.

**The producers.**
- `honesided` is `CompressorRelativeData.oneSided`. `Bad` consists of the matched
  objects whose match has an orbit meeting the unretained objects in more than the
  scale `cleanScale`, a slowly vanishing multiple of the unretained density.
- `hmedian` is `CompressorRelativeData.concentrated_of_oneSided`, one application of
  `blockRatio_negligible`.
- `hcounting` is `CompressorRelativeData.transported`.

**What this does not give.** These producers do not build the relative data
(`hfunctor`), bound the Hamming distance (`hhamming`) or represent almost
centralizers by bisections (`hrep`). Those are other lanes' hypotheses of the same
skeleton. So this node does not derive `kun-thom-sofic-centralizer-normalization`.

Derivation: `kt-counting-props-producers-proof`.
