---
rg: 2
id: fpbs-universal-optimistic-certificate-route
kind: route
title: Contradict the query strong converse with the missing optimistic certificate construction
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-universal-optimistic-certificate-budget
  - fpbs-optimistic-search-certified-growth
  - fpbs-bounded-query-connection-strong-converse
artifacts:
  - research/artifacts/fpbs/optimistic-search.md
  - research/artifacts/fpbs/query-strong-converse.md
---

This is a proved conditional implication, not an unconditional proof.
Fix any Cayley graph in the universal goal and suppose p_c=p_u=c.
The OPEN budget premise supplies q,b and finite planning caps M_n.
The certified-growth result establishes sound open-path certificates
for this algorithm; finite planning and query caps make it a bounded
experiment with no unqueried percolation information in its seed.
The strong converse therefore gives, for some eta>0,

    P_q(search returns a path) <= exp(-eta*n)

for every n, because b<lambda/k(q,c). This contradicts the zero
limsup exponential rate in the budget premise. Hence equality of the
thresholds is impossible for each graph. Since p_c<=p_u, they are
strictly separated, and the threshold classification stated in the
universal goal gives the requested interval with infinitely many
infinite clusters. The open budget premise is the sole unresolved
input of this route; none of the finite computations proves it.
