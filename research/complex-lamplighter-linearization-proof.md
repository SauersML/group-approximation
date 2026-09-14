---
rg: 2
id: complex-lamplighter-linearization-proof
kind: route
title: Pull back locally constant functions, compare traces, and pass normality to absolute continuity
target: complex-lamplighter-linearizations-are-normal-iff-surjective
requires: []
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

Theorem C, Section 1.3 of the artifact.

1. **Dictionary.** Characters of `L = (+)_G Z/q` span `LC(A^G)`, so `LC(A^G) x|_alg G = C[Z/q wr G]`. Pullback along `tau`
   is a shift-commuting *-homomorphism.
2. **Injective iff surjective pullback.** An injective automaton is a homeomorphism onto its closed image, and clopen
   sets of the image extend. A nonzero locally constant function vanishing on the image exists iff the image is
   proper.
3. **Traces.** `tr(f o tau) = integral f d(tau_* lambda)`, and the support of `f o tau` is `tau^-1(supp f)`.
4. **Normality.**
   - (a) => (b): bijective automata preserve `lambda`.
   - (b) => (c): trace preservation gives an isometry of `L^2(tr)`, hence a normal extension.
   - (c) => (d): clopens decreasing to a `lambda`-null compact set of positive `nu`-measure contradict weak
     continuity.
   - (d) => (a): an invariant measure absolutely continuous with respect to the ergodic `lambda` equals `lambda`, and a
     closed set of full measure is everything.

The ergodicity step uses that `G` is infinite. Uses `bijective-ca-preserve-uniform-bernoulli-measure` only for
(a) => (b), which is standard over every group.
