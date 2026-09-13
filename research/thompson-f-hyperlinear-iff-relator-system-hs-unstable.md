---
rg: 2
id: thompson-f-hyperlinear-iff-relator-system-hs-unstable
kind: claim
title: Thompson's F is nonhyperlinear exactly when unitary almost-solutions of its two relators almost commute
distinct_from:
  thompson-f-sofic-iff-relator-system-unstable: that is the Hamming statement for permutations and soficity; this is the normalized Hilbert--Schmidt statement for unitary matrices and hyperlinearity.
  thompson-v-ce-one-word-trace-face-is-binary: that is the one-word HS form for the simple group V, where the correction is to the trivial representation; this is F, corrected through HS-stability of its abelianization Z^2.
  hyperlinear-hs-stable-is-residually-finite: that is the general one-directional principle; this adds the converse for F from its character classification.
artifacts:
  - research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md
---

**ESTABLISHED (unreviewed).** For `F = <a, b | [ab^-1, a^-1ba], [ab^-1, a^-2ba^2]>` the following are
equivalent.
1. `F` is not hyperlinear.
2. The relator system is stable for unitary matrices in normalized Hilbert--Schmidt norm, uniformly in
   the dimension.
3. For every `epsilon > 0` there is `delta > 0` such that all `U, W in U(n)` satisfying both relators
   within `delta` in `||.||_2` have `||UW - WU||_2 < epsilon`.

**Mechanism** (artifact, Section 5).
- **Character.** The trace character of an HS almost-representation is `t tau_reg + (1-t) chi_ab`
  (`thompson-f-character-simplex`).
- **`t > 0`.** Tensor powers times the regular representation of a `Z^2`-torus give a separating HS
  approximation.
- **`t = 0`.** The generators almost commute, and HS-stability of `Z^2`
  (`chordal-abelian-graph-products-hs-stable`) supplies exact commuting solutions.

Since `F <= V`, statement 3 also makes `V` nonhyperlinear
(`thompson-v-not-hyperlinear-from-f-not-hyperlinear`).

Derivation: `thompson-f-hyperlinear-iff-relator-system-hs-unstable-proof`.
