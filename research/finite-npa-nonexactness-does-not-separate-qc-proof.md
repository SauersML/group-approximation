---
rg: 2
id: finite-npa-nonexactness-does-not-separate-qc-proof
kind: route
title: A strictly decreasing family need not have any member equal to its limit
target: finite-npa-nonexactness-does-not-separate-qc
requires: []
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

**Complete direct argument.**  Convergence of the hierarchy gives
`intersection over k of Q_k = Q_c`, and the levels are nested,
`Q_(k+1)` contained in `Q_k`.  Suppose `closure(Q) = Q_c`.  Then for each `k`,
`Q_k` properly contains `Q_c` unless the intersection is attained at level `k`;
attainment at any single level is a strictly stronger property than convergence
and is exactly what the cited theorems refute.  So both hypotheses
`closure(Q) = Q_c` and "every `Q_k` strictly contains `closure(Q)`" hold
simultaneously in a perfectly consistent picture, and the non-exactness
statements cannot distinguish it from the picture where the two sets differ.

Formally: the implication "for all `k`, `Q_k != closure(Q)`" implies
"`closure(Q) != Q_c`" would require some `Q_k` to equal `Q_c`, which convergence
does not supply.  Hence no such implication.

Nothing about the specific constructions is used, so the conclusion applies to
any future finite-level non-exactness result in this or any other scenario.
