---
rg: 2
id: strict-pair-table-realization-proof
kind: route
title: Pull configurations on the realizing group back to patterns on the product tables
target: strict-pairs-transfer-to-table-realizations
requires: []
artifacts:
  - research/artifacts/gottschalk-table-realization-and-evasion-2026-09-12.md
---

Derivation: Section 1 of the linked artifact.

- **The identity is fixed.** `phi(1) = 1`, because `1` lies in both `S` and `M`.
- **Decoder identity.** At `k in K`, `sigma_K tau_K(z)(k)` reads `z` at the cells
  `k phi(sm)`. The function `x(c) = z(k phi(c))` on `SM` is a pattern on a subset of
  `G`, whatever collisions `phi` has. Extend it and apply `sigma tau = id` at `1`.
  This gives `x(1) = z(k)`.
- **Orphan.** Suppose `z` displays the moved pattern on `phi(Omega)`. Pulling `z`
  back along `phi` gives a pattern on `Omega M` that displays `p` on `Omega`, which
  is impossible.
- **Corollaries.**
  - (1) An injective partial table is a realization.
  - (2) A homomorphism restricted to `F` is multiplicative. So it is a realization
    unless it merges a distinguished pair.
  - (3) The table group realizes its own tables, and its map to `G` separates
    `Omega`.
