---
rg: 2
id: sofic-radical-localizes-garden-of-eden-windows-proof
kind: route
title: Run Gromov--Weiss counting along amplified models that separate every window difference
target: sofic-radical-localizes-garden-of-eden-windows
requires: []
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

Self-contained derivation; the artifact gives every constant.

1. `Rad(G)` is normal, and trivial iff `G` is sofic. The nontrivial direction
   amplifies: a disjoint union of models, one per element, then an `r`-fold
   product, where fixed fractions multiply and defects add.
2. Suppose no difference `k^-1 k'` of distinct window cells is invisible. The
   same amplification gives, for every `delta`, an `(F, r delta)`-model, with
   `r` fixed, in which these differences fix at most a quarter of the points in
   total. So injective window charts have density at least `3/4 - beta`, where
   `beta` bounds the bad-point fraction.
3. At good points the model decoder recovers the input, so the model automaton
   has at least `|A|^((1-beta)|V|)` outputs. On a maximal family of disjoint
   injective charts, of size at least `(3/4-beta)|V|/|Omega|^2`, every output
   avoids `p`. This caps the outputs at `|A|^|V| (1-|A|^-|Omega|)^|C|`.
4. As `delta -> 0` the two bounds contradict each other.

Passing to the memory subgroup uses the coset decomposition of the image: a
Garden of Eden restricts to one within a single coset of `<M>`.
