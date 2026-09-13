---
rg: 2
id: artin-sigma1-conjecture-via-dead-edge-rings
kind: route
title: "Dead route: the Sigma^1-conjecture from universal existence of dead-edge rings"
target: artin-sigma1-is-connected-dominant-living-subgraph
requires:
  - every-artin-dead-cut-admits-a-nonzero-dead-edge-ring
  - artin-sigma1-dead-edge-ring-obstruction
  - artin-sigma1-living-subgraph-bounds
---

Derivation, valid but with a refuted premise.

1. By Almeida–Kochloukova's reduction (quoted in the target) it suffices to treat
   discrete `χ` with `Liv_0^χ` connected and dominant and `Liv^χ` disconnected.
2. The universal premise supplies a ring witness, and the obstruction gives
   `[χ] ∉ Σ^1`.
3. Meier's inclusion then gives equality.

Dead: its first premise is refuted by the graph `K`.
