---
rg: 2
id: zpc-irs-value-computable-upper-hierarchy
kind: claim
title: ZPC-IRS value of a finite tailored game has a computable decreasing hierarchy
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that uses this hierarchy in an undecidability diagonalization; this is the effective compactness statement for one arbitrary tailored game.
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
---

For every finite tailored non-local game `G`, define `omega_ZIRS(G)` by
restricting Manzoor IRS strategies to those for which every readable variable
is Z-aligned almost everywhere and every pair of variables belonging to the
endpoints of a game edge commute almost everywhere.

Then there is a computable sequence of rational linear-program optima

```text
alpha_1^Z(G) >= alpha_2^Z(G) >= ... -> omega_ZIRS(G).
```

In stabilizer-IRS coordinates the extra ZPC conditions are finite cylinder
equations:

```text
Pr[u in H or Ju in H]=1              for readable u,
Pr[[u,v] in H]=1                     along game edges.
```

They can therefore be added to Manzoor's computable random-pseudo-subgroup
polytopes without changing the restriction/compactness proof of convergence.
