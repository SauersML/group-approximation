---
rg: 2
id: fpbs-closed-wall-forces-exponential-search
kind: claim
title: A finite closed wall forces exponential target-directed search cost on T4 times Z
artifacts:
  - research/artifacts/fpbs/search-barriers.md
---

For every finite beta>=0, the balanced search with priority
depth(u)+1+beta*d(v,opposite root) on T_4 x Z requires at least
3^(m+1)-m-3 fresh queries when the copies of one tree edge at heights
|z|<=m are closed and every other edge is open. Its roots are the
height-zero endpoints of that tree edge; shortest open distance is
2m+3. This is a deterministic obstruction, not a Bernoulli mean bound.

Corollary 1.1 strengthens the obstruction: uniformly in m, the open
configuration has edge Cheeger constant at least 2 and normalized
edge Cheeger constant at least 1/3. Every open edge lies on an open
four-cycle, and iterative leaf removal changes nothing. Thus positive
expansion and the absence of dangling bridges do not give a polynomial
detour bound for this search schedule.
