---
rg: 2
id: fpbs-reduced-circulation-tail-bounds-cost-excess-proof
kind: route
title: Span the cycle space by routed relators and split it at the reduced-mass threshold
target: fpbs-reduced-circulation-tail-bounds-cost-excess
requires:
  - fpbs-short-cycle-edge-measure-vanishes-near-optimum
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
---

Sections 5 and 6 of the artifact, Theorem 5.1 and Corollary 6.1. Replacing each graphing edge of a finite closed walk by its canonical word shows every finite cycle chain lies in the span of the routed relator circulations and the edge-comparison loops; freeness is used to conclude that the canonical word represents the identity. A circulation of reduced mass at most L decomposes into simple cycles of length at most L, so it lies in the short-cycle span; the remaining vectors are indexed by domains of total measure T_L, and truncating to roots with representing walks of bounded length keeps the relevant boundary maps bounded before taking increasing closed spans. The descent statement then applies the surgery inequality to the short-cycle support. This is a supplied deduction, not external validation.
