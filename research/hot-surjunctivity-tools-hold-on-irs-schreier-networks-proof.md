---
rg: 2
id: hot-surjunctivity-tools-hold-on-irs-schreier-networks-proof
kind: route
title: Coset-minimal representatives give mass transport; the group proofs then run per graph, with base-measurable markers
target: hot-surjunctivity-tools-hold-on-irs-schreier-networks
requires: []
artifacts:
  - research/artifacts/design-subgroup-tests-2026-09-17.md
---

Complete direct proof: artifact Section 5.

1. **Mass transport** (5.1).
   - Sum over group elements that are least in their coset.
   - Substitute `H' = g^-1 H g`, using `(X_H, H, Hg) = (X_{H'}, H' g^-1, H')`.
   - Exactly one `u` per vertex has `u^-1` least in `u^-1 H'`.
2. **Bernoulli preservation** (5.2). `sigma pi tau` is a fibrewise permutation of a finite window. So `tau_*` of
   the uniform measure is invariant under local permutations.
3. **Transport** (5.3). The input side is the chain rule over the decoder ball. The output side follows by item 1.
   The domination equivalence is algebra.
4. **Rokhlin deficit** (5.4).
   - Markers: reverse-bad vertices whose base label is least among reverse-bad vertices within `2 rho`. Their
     density is at least `delta / b_(2 rho)`, and they are base-measurable.
   - At each marker the image avoids a `rho`-ball pattern.
   - Recording marker patterns, blanks and coordinates gives a relatively generating partition. Mass transport
     bounds its entropy.
