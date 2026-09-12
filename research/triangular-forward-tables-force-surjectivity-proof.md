---
rg: 2
id: triangular-forward-tables-force-surjectivity-proof
kind: route
title: Eliminate letters downward to a free table group and transfer its surjectivity by the table-group homomorphism
target: triangular-forward-tables-force-surjectivity
requires:
  - strict-automata-live-on-canonical-table-groups
  - residually-finite-groups-are-surjunctive
artifacts:
  - research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md
---

Section 4 of the artifact.

1. Downward Tietze elimination keeps each `x_i` once in `r_i` and absent later,
   because the substituted words come from later relators, which avoid `x_i`. So
   `U_E` is free.
2. Free groups are residually finite, hence surjunctive.
3. Over `U_E` the realization is injective by forward sufficiency, hence surjective,
   so its reverse table is reverse sufficient.
4. By the table-group homomorphism and coarsening, every realization whose forward
   table dominates `E` inherits the reverse identity.
