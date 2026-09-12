---
rg: 2
id: fpbs-optimistic-search-linear-wall-cost
kind: claim
title: Optimistic replanning crosses the finite wall in exactly five m plus four edge queries
artifacts:
  - research/artifacts/fpbs/optimistic-search.md
---

On the T_4 x Z wall configuration closing the copies of xy at |z|<=m,
the forward optimistic shortest-path search uses exactly 5m+4 queries
and certifies a shortest open path of length 2m+3. Thus it avoids the
exponential query obstruction for the previous scalar-priority schedule.
This is a deterministic calibration, not a universal Bernoulli cost bound.
