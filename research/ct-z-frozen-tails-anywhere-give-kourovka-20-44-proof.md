---
rg: 2
id: ct-z-frozen-tails-anywhere-give-kourovka-20-44-proof
kind: route
title: "Frozen sets shift by the cocycle; the frozen set bounds the shift above and the tracked position bounds it below, giving a uniform count per orbit and positive-density minima"
target: ct-z-frozen-tails-anywhere-give-kourovka-20-44
requires:
  - ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44
  - ct-z-orbit-transversal-dichotomy-is-collatz-hard
---

Lane proof (bh-free-58, 2026-09-19), not reviewed. The body of
`ct-z-frozen-tails-anywhere-give-kourovka-20-44` proves Lemma 1 (frozen sets shift by the
cocycle) and Lemma 2 (uniform count). It uses:
- from the ray node: tracking, reversal and prefix dependence, which need no ray hypothesis, and
  the corner argument, for the positive-ray row;
- the Collatz-hardness node, for the `G_T` corollary.
