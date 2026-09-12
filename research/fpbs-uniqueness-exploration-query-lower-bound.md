---
rg: 2
id: fpbs-uniqueness-exploration-query-lower-bound
kind: claim
title: Uniqueness near criticality forces quadratic conditional edge-query cost per walk step
artifacts:
  - research/artifacts/fpbs/exploration-information.md
---

For a fixed nonamenable Cayley graph, put c=p_c and lambda=-log rho for
its lazy walk. At any uniqueness parameter c<q<1, every balanced
exhaustive two-ended connection search satisfies
liminf_n E_q[N_n | both endpoint clusters infinite]/n >= lambda/k(q,c).
Along uniqueness parameters q down to c the scaled lower bound is
liminf (q-c)^2 B_A(q)>=2c(1-c)lambda. Sections 2-4 prove this necessary
condition. No conflicting algorithmic upper bound is established.
