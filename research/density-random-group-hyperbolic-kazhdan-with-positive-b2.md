---
rg: 2
id: density-random-group-hyperbolic-kazhdan-with-positive-b2
kind: claim
title: Hyperbolic Kazhdan groups with a finite aspherical two-complex and positive second Betti number exist
distinct_from:
  torsion-free-hyperbolic-kazhdan-partner-exists: that is existence of a torsion-free non-elementary hyperbolic Kazhdan group with no homological clause; this adds a finite aspherical 2-dimensional presentation complex and b_2 >= 1.
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that is the open conjecture that some such group is flexibly HS-stable; this only supplies the candidate class, with no stability content.
artifacts:
  - research/artifacts/density-random-groups-b2-verified-2026-09-12.md
---

**ESTABLISHED.** Fix `m >= 2` and `d ∈ (1/3, 1/2)`. Consider the Gromov
density model `G = <a_1, …, a_m | R>` with `R` a uniformly random set of
`⌊(2m−1)^{dℓ}⌋` cyclically reduced words of length `ℓ`. With probability
tending to 1 as `ℓ → ∞` through multiples of 3:

- `G` is infinite, torsion-free, word-hyperbolic and Kazhdan;
- its presentation 2-complex is a finite `K(G,1)`;
- `b_2(G; Q) = |R| − m >= 1`.

In particular such groups exist. This is existence with high probability; no
specific presentation is certified.

This is the candidate class listed under "Candidates" in
`kazhdan-hyperbolic-b2-group-flexibly-hs-stable`, now source-verified. The
proof is `density-random-group-positive-b2-proof`.
