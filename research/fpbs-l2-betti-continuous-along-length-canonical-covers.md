---
rg: 2
id: fpbs-l2-betti-continuous-along-length-canonical-covers
kind: claim
title: The first L2 Betti number of a finitely generated group is the limit over its length-canonical finitely presented covers
distinct_from:
  fpbs-bernoulli-cost-lsc-along-length-canonical-covers: that is the cost statement; this is the pure L2 statement, and the two are equivalent only under cost-Betti
  fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers: that shows beta_1 jumps from 0 to 1 along arbitrary finitely presented covers; this asks for continuity along F/<<N cap B_R>>
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

**OPEN.** For every finitely generated marked group `G = F/N`, `beta_1^(2)(F/<<N cap B_R>>) -> beta_1^(2)(G)`.

Pichot's theorem gives `limsup <= beta_1(G)`. The open part is `beta_1(G) <= liminf`.

- For arbitrary finitely presented covers the lower bound is false (`E_R -> (Z wr Z) * Z`).
- The length-canonical covers of `(Z wr Z) * Z` satisfy it.
- Heuristically, moment methods fail because the relator cells at level `R` have length up to `R`.

Artifact, Section 3.
