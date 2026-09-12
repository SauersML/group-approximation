---
rg: 2
id: fpbs-uniqueness-query-quantiles-and-tube-width-proof
kind: route
title: Apply Borel-Cantelli to certificate costs and count the edges in a walk tube
target: fpbs-uniqueness-query-quantiles-and-tube-width
requires:
  - fpbs-bounded-query-connection-strong-converse
artifacts:
  - research/artifacts/fpbs/query-strong-converse.md
---

Sections 2 through 4 prove the conclusions. FKG gives P(I_n)>=theta^2,
so conditioning costs only that factor. Summable exponential bounds
and a countable sequence of budgets give the almost sure statement.
Taylor expansion and a fixed optimized Renyi order give the near-critical
constant. Exposing a whole tube costs at most d(n+1)|B_R|/2 queries;
the strong converse and the elementary ball-volume upper bound imply
the necessary volume and radius constraints.
