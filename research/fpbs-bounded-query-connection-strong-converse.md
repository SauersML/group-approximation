---
rg: 2
id: fpbs-bounded-query-connection-strong-converse
kind: claim
title: A path certificate below the critical information budget has exponentially small probability
artifacts:
  - research/artifacts/fpbs/query-strong-converse.md
---

Let c=p_c and lambda=-log rho for the independent lazy walk on a
nonamenable Cayley graph. For 0<c<q<1 and alpha>1, the probability
that an adaptive algorithm certifies o connected to X_n in at most
m fresh queries is at most
exp(-(alpha-1)(lambda*n-m*D_alpha(q||c))/alpha).
The seed is independent of percolation and the rule is the same under
c and q. Thus any linear budget b<lambda/k(q,c) gives exponential
decay. Sections 1 and 2 also give the exact binomial testing bound.
