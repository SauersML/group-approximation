---
rg: 2
id: fpbs-green-visit-criterion-implies-nonuniqueness
kind: claim
title: Finite expected walk visits to the cluster of the origin at a parameter rule out uniqueness up to that parameter
distinct_from:
  fpbs-pivotal-nonconcentration-implies-nonuniqueness: that needs exponential decay of a_n at some p above p_c; this needs only summability of a_n.
---

Theorem 3.1(a) of
`research/artifacts/fpbs/docs/green-visit-kernel-2026-09-17.md`.

Let `G` be any Cayley graph and `X_n` the simple or lazy random walk,
independent of the percolation. Let `a_n(p)=P_p(e<->X_n)` and
`A(p)=sum_n a_n(p)`. If `A(p)<infinity`, then no `p'<=p` has a unique
infinite cluster. If moreover `p>p_c`, then `p_u>=p>p_c`.
