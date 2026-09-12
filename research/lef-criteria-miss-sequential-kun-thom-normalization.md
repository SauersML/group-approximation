---
rg: 2
id: lef-criteria-miss-sequential-kun-thom-normalization
kind: claim
title: The formalized LEF criteria and exact collapses miss sequential Kun--Thom normalization at mass and at size
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Kun--Thom Theorem 4.1 itself; this records why the repository's LEF criteria and exact collapses do not prove its sequential per-compressor form, and which stages of the section 4 proof cannot be skipped.
  kun-thom-expander-centralizer-formalized: that is the formalized single-expander theorem concluding LEF of a commuting factor; this shows its hypotheses fail for an arbitrary almost-centralizing sequence and its conclusion is empty there.
  invariant-size-collapse: that is the exact collapse under a conjugation-invariant size; this records that sofic approximations carry no such size at Hamming scale, with an integer-index example showing that conservation along the compressor does not replace the median step.
  relative-normalization-modulo-kazhdan-kernel: that is the relative normalization question modulo a normal Kazhdan kernel; this audits shortcuts to the absolute sequential core consumed by the Bowen--Chapman endpoint.
artifacts:
  - research/artifacts/kt41-alt-route-2026-09-12.md
---

Let `Gamma <= G` be an infranormal pair of Kazhdan groups, `t` a compressor, `A` a
sofic approximation of `G`, `v` a sequence of model permutations almost commuting with
`A(Gamma)`, and `w = A(t) v A(t)^-1`. The Lean core `SeqNormalizes Gamma t` asks that `w`
almost commutes with `A(Gamma)`.

1. **Single-expander theorem.**
   - `KunThomTheorem.isLEF_of_exactProductExpansion` needs a `SoficApproximation (K x J)`
     and a Cheeger bound on the whole model.
   - For `Gamma x <v>` neither hypothesis holds for an arbitrary `v`, and its conclusion
     `IsLEF Z` is empty.
   - Its per-component content is the improvement step already landed as
     `CentralizerNormalizationImprove`.
2. **Compression criterion.**
   - `isLEF_of_ambientDecomposition` and `isLEF_of_soficApproximation` certify, through
     `SelectionOutput`, one selected expanding component of positive mass.
   - Normalization needs almost all of the mass. A compressor carries components
     `C_i` to `C_(pi i)`, so equality of cluster groups on different objects is a
     conservation statement over the whole mass.
   - With the trivial commuting factor of `CompressionSetup.ofCompressor`, the
     conclusion is empty.
3. **Exact collapses.** `ExactCompression`, `FiniteQuotientBlindness`,
   `CommutantRigidity`, `FiniteDimensionalKill` and `FreeLampRigidity` all collapse
   under an exact size. No such size is preserved at normalized Hamming scale.
4. **Integer-index example.** Take a `pi`-cycle of `L` objects of mass `1/L` and size
   `2^L`, with isotropy `k = 2^(L-1), ..., 2, 1` and one jump back.
   - The exceptional mass is `1/L`.
   - The observables `1/k` and `k/|C|` are conserved along `pi` up to `O(1/L)`.
   - Yet the index `k(i)/k(pi i)` is `2` on mass `1 - 1/L`, and `log |Y| ~ L`.
   - So conservation of bounded observables, or of `log k` without a rate
     `o(1/log |Y_n|)` on the exceptional mass, cannot force index one. The clamp and
     median pinning with property (T) of `G` is needed.

Consequence: every stage of the section 4 route in
`research/artifacts/kt-theorem-4-1-blueprint-2026-09-12.md` is load-bearing:
- cluster groupoid with improvement;
- relative functor;
- median step;
- integrality counting;
- patching and the Hamming estimate.

The artifact also records two savings inside that route: one median application to the
Hom-count `o k`, and a doubling reduction to involutive sequences.

Derivation: `lef-criteria-miss-sequential-kun-thom-normalization-proof`.
